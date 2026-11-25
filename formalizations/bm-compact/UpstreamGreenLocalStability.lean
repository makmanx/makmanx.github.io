import GradientAnalyticBatch
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Actual local gradient stability for two weak solutions with the same
constant source. A compact full-W0 difference test, genuine p-monotonicity
and actual Holder flux bounds turn a scalar uniform gap into an Lp gradient
energy bound. The local geometric constant is chosen before either field.
No gradient closeness, energy conclusion, or classical regularity is input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem green_integral_norm_power
    {n : ℕ} {p : ℝ} {μ : Measure (Space n)} {g : Space n → Space n}
    (hp : 1<p) (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫ x,‖g x‖^p ∂μ)=(eLpNorm g (ENNReal.ofReal p) μ).toReal^p := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have ht := BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp) (hg.toLp g)
  rw [Lp.norm_toLp] at ht
  have he := integral_congr_ae (hg.coeFn_toLp.fun_comp (fun v => ‖v‖^p))
  exact (ht.trans he).symm

private theorem green_flux_L1_bound
    {n : ℕ} {p : ℝ} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    {g : Space n → Space n} (hp : 1<p) (hg : MemLp g (ENNReal.ofReal p) μ) :
    Integrable (fun x => ‖pFlux p (g x)‖) μ ∧
      (∫ x,‖pFlux p (g x)‖ ∂μ)≤(μ.real univ)^(1/p)*
        (eLpNorm g (ENNReal.ofReal p) μ).toReal^(p-1) := by
  let q : ℝ := p/(p-1)
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hq1 : 1<q := (Real.holderConjugate_iff.mp hpq.symm).1
  have hF := (memLp_pFlux hp hg).norm
  have hF1 := hF.mono_exponent (ENNReal.one_le_ofReal.mpr hq1.le)
  refine ⟨memLp_one_iff_integrable.mp hF1,?_⟩
  have hH := integral_mul_norm_le_Lp_mul_Lq hpq.symm hF (memLp_const (1:ℝ))
  simp only [Real.norm_eq_abs,abs_norm,abs_one,mul_one,Real.one_rpow,integral_const,
    smul_eq_mul,mul_one] at hH
  have hpower : (∫ x,‖pFlux p (g x)‖^q ∂μ)=
      (eLpNorm g (ENNReal.ofReal p) μ).toReal^p := by
    simpa only [q,norm_pFlux_dual_power hp] using green_integral_norm_power hp hg
  rw [hpower,←Real.rpow_mul ENNReal.toReal_nonneg] at hH
  have he : p*(1/q)=p-1 := by
    dsimp only [q]
    field_simp
  rw [he] at hH
  simpa only [mul_comm] using hH

set_option maxHeartbeats 1800000 in
/-- Fixed local geometry supplies a genuine Lp weak-gradient stability
constant before both actual weak solutions and their scalar uniform gap.
The source is the same arbitrary real constant for both fields. -/
theorem exists_local_gradient_stability_constant
    {n : ℕ} {p : ℝ} (hp : 2≤p) {U D : Set (Space n)}
    (hU : IsOpen U) (hD : LocalDomain D U) :
    ∃ C : ℝ,0≤C ∧ ∀ (c : ℝ) (u v : Space n → ℝ) (g h : Space n → Space n),
      WeakPSourcePair p c U u g → WeakPSourcePair p c U v h →
      SobolevPair p U u g → SobolevPair p U v h →
      ∀ δ : ℝ,0≤δ → (∀ x∈U,|u x-v x|≤δ) →
        Integrable (fun x => ‖g x-h x‖^p) (volume.restrict D) ∧
        (∫ x in D,‖g x-h x‖^p)≤C*δ*
          ((eLpNorm g (ENNReal.ofReal p) (volume.restrict U)).toReal+
           (eLpNorm h (ENNReal.ofReal p) (volume.restrict U)).toReal)^(p-1) := by
  have hp1 : 1<p := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) hp
  have hp0 : 0<p := zero_lt_one.trans hp1
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨r,hr,hthick⟩ := hK.exists_cthickening_subset_open hU hD.2.2
  let V : Set (Space n) := thickening r (closure D)
  have hV : LocalDomain V U := by
    refine ⟨isOpen_thickening,hK.isBounded.thickening,?_⟩
    exact (closure_thickening_subset_cthickening r (closure D)).trans hthick
  have hDV : D⊆V := subset_closure.trans (self_subset_thickening hr (closure D))
  have hVU : V⊆U := subset_closure.trans hV.2.2
  obtain ⟨a,ha⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hV.1
    (self_subset_thickening hr (closure D))
  let η : Space n → ℝ := fun x => Real.smoothTransition (a x)
  have hη : SmoothTest V η := ⟨Real.smoothTransition.contDiff.comp ha.1,
    ha.2.1.comp_left (Real.smoothTransition.zero_of_nonpos (le_refl (0:ℝ))),
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0:ℝ))) a).trans ha.2.2.1⟩
  let χ : Space n → ℝ := fun x => η x*η x
  have hχ : SmoothTest V χ :=
    ⟨hη.1.mul hη.1,hη.2.1.mul_right,tsupport_mul_subset_left.trans hη.2.2⟩
  have hχ0 (x : Space n) : 0≤χ x := mul_self_nonneg _
  have hχ1 (x : Space n) (hx : x∈D) : χ x=1 := by
    have hη1 : η x=1 := Real.smoothTransition.one_of_one_le (ha.2.2.2 x (subset_closure hx))
    simp only [χ,hη1,mul_one]
  have hgc : Continuous (gradient χ) := continuous_gradient_of_contDiff_one (hχ.1.of_le (by simp))
  obtain ⟨P,hP,hPb⟩ := ((BMCompactCapacityV2.gradient_hasCompactSupport hχ.2.1).isCompact_range hgc).isBounded.exists_pos_norm_le
  have hPx (x : Space n) : ‖gradient χ x‖≤P := hPb _ (mem_range_self x)
  let A : ℝ := (volume.real V)^(1/p)
  let α : ℝ := (1/2:ℝ)^p
  have hA : 0≤A := Real.rpow_nonneg (measureReal_nonneg) _
  have hα : 0<α := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<1/2) _
  let C : ℝ := (p*P*2*A)/(4*α)
  refine ⟨C,div_nonneg (by positivity) (by positivity),?_⟩
  intro c u v g h hu hv su sv δ hδ hgap
  letI : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hV.2.1.measure_lt_top.ne
  have hgV := su.2.2.1.mono_measure (Measure.restrict_mono_set volume hVU)
  have hhV := sv.2.2.1.mono_measure (Measure.restrict_mono_set volume hVU)
  have hNraw := integrable_norm_rpow_of_memLp hp1 (hgV.sub hhV)
  have hNI : Integrable (fun x => ‖g x-h x‖^p) (volume.restrict V) := by
    simpa only [Pi.sub_apply] using hNraw
  have hχtop : MemLp χ (∞:ℝ≥0∞) (volume.restrict V) :=
    hχ.1.continuous.memLp_top_of_hasCompactSupport hχ.2.1 _
  have hLI : Integrable (fun x => χ x*‖g x-h x‖^p) (volume.restrict V) := by
    simpa only [Pi.mul_apply,mul_comm] using! hNI.mul_of_top_right hχtop
  have hID := hNI.mono_measure (Measure.restrict_mono_set volume hDV)
  refine ⟨hID,?_⟩
  have hdom : (∫ x in D,‖g x-h x‖^p)≤∫ x in V,χ x*‖g x-h x‖^p := by
    calc
      _=∫ x in D,χ x*‖g x-h x‖^p := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
        rw [hχ1 x hx,one_mul]
      _≤_ := integral_mono_measure (Measure.restrict_mono_set volume hDV)
        (Eventually.of_forall (fun x => mul_nonneg (hχ0 x) (Real.rpow_nonneg (norm_nonneg _) _))) hLI
  obtain ⟨hFgI,hFg⟩ := green_flux_L1_bound hp1 hgV
  obtain ⟨hFhI,hFh⟩ := green_flux_L1_bound hp1 hhV
  let S := (eLpNorm g (ENNReal.ofReal p) (volume.restrict U)).toReal+
    (eLpNorm h (ENNReal.ofReal p) (volume.restrict U)).toReal
  have hNg : (eLpNorm g (ENNReal.ofReal p) (volume.restrict V)).toReal≤S :=
    (ENNReal.toReal_mono su.2.2.1.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hVU))).trans
        (le_add_of_nonneg_right ENNReal.toReal_nonneg)
  have hNh : (eLpNorm h (ENNReal.ofReal p) (volume.restrict V)).toReal≤S :=
    (ENNReal.toReal_mono sv.2.2.1.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hVU))).trans
        (le_add_of_nonneg_left ENNReal.toReal_nonneg)
  have hflux : (∫ x in V,‖pFlux p (g x)‖)+(∫ x in V,‖pFlux p (h x)‖)≤2*A*S^(p-1) := by
    have hgPow := Real.rpow_le_rpow ENNReal.toReal_nonneg hNg (by linarith : 0≤p-1)
    have hhPow := Real.rpow_le_rpow ENNReal.toReal_nonneg hNh (by linarith : 0≤p-1)
    have hgB : (∫ x in V,‖pFlux p (g x)‖)≤A*(eLpNorm g (ENNReal.ofReal p) (volume.restrict V)).toReal^(p-1) := by
      simpa only [A,Measure.real,Measure.restrict_apply_univ] using hFg
    have hhB : (∫ x in V,‖pFlux p (h x)‖)≤A*(eLpNorm h (ENNReal.ofReal p) (volume.restrict V)).toReal^(p-1) := by
      simpa only [A,Measure.real,Measure.restrict_apply_univ] using hFh
    calc
      _≤A*(eLpNorm g (ENNReal.ofReal p) (volume.restrict V)).toReal^(p-1)+
          A*(eLpNorm h (ENNReal.ofReal p) (volume.restrict V)).toReal^(p-1) := add_le_add hgB hhB
      _≤A*S^(p-1)+A*S^(p-1) := add_le_add
        (mul_le_mul_of_nonneg_left hgPow hA) (mul_le_mul_of_nonneg_left hhPow hA)
      _=2*A*S^(p-1) := by ring
  obtain ⟨-,hcrossI,-⟩ := hu.local_flux_difference_identity hv hV hχ
  have hcross := integral_mono_ae hcrossI.neg ((hFgI.add hFhI).const_mul (δ*P)) (by
    filter_upwards [ae_restrict_mem hV.1.measurableSet] with x hx
    change -((u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x))≤
      (δ*P)*(‖pFlux p (g x)‖+‖pFlux p (h x)‖)
    calc
      _≤|(u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)| := neg_le_abs _
      _=|u x-v x| * |inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)| := abs_mul _ _
      _≤δ*(‖pFlux p (g x)-pFlux p (h x)‖*‖gradient χ x‖) :=
        mul_le_mul (hgap x (hVU hx)) (abs_real_inner_le_norm _ _) (abs_nonneg _) hδ
      _≤δ*((‖pFlux p (g x)‖+‖pFlux p (h x)‖)*P) := mul_le_mul_of_nonneg_left
        (mul_le_mul (norm_sub_le _ _) (hPx x) (norm_nonneg _)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))) hδ
      _=_ := by ring)
  change (∫ x in V,-((u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)))≤
    ∫ x in V,(δ*P)*(‖pFlux p (g x)‖+‖pFlux p (h x)‖) at hcross
  rw [integral_neg,integral_const_mul,integral_add hFgI hFhI] at hcross
  have henergy := hu.local_gradient_difference_bound hv hp hV hχ hχ0
  have hscale : (∫ x in V,χ x*‖(1/2:ℝ) • (g x-h x)‖^p)=
      α*(∫ x in V,χ x*‖g x-h x‖^p) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      change χ x*‖(1/2:ℝ) • (g x-h x)‖^p=α*(χ x*‖g x-h x‖^p)
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),
        Real.mul_rpow (by norm_num : (0:ℝ)≤1/2) (norm_nonneg _)]
      dsimp only [α]
      ring)
  rw [hscale] at henergy
  have hEc : (4*α)*(∫ x in D,‖g x-h x‖^p)≤p*((δ*P)*(2*A*S^(p-1))) := by
    calc
      _≤(4*α)*(∫ x in V,χ x*‖g x-h x‖^p) := mul_le_mul_of_nonneg_left hdom (by positivity)
      _=4*(α*(∫ x in V,χ x*‖g x-h x‖^p)) := by ring
      _≤-p*(∫ x in V,(u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)) := henergy
      _=p*(-(∫ x in V,(u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x))) := by ring
      _≤p*((δ*P)*((∫ x in V,‖pFlux p (g x)‖)+(∫ x in V,‖pFlux p (h x)‖))) := mul_le_mul_of_nonneg_left hcross hp0.le
      _≤_ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hflux (mul_nonneg hδ hP.le)) hp0.le
  have hden : 0<4*α := by positivity
  calc
    (∫ x in D,‖g x-h x‖^p)≤(p*((δ*P)*(2*A*S^(p-1))))/(4*α) :=
      (le_div_iff₀ hden).mpr (by nlinarith only [hEc])
    _=C*δ*S^(p-1) := by dsimp only [C];ring

end BMCompactPDE
#print axioms BMCompactPDE.exists_local_gradient_stability_constant
