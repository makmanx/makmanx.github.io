import GradientAnalyticBatch
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Actual local gradient stability for two weak solutions with the same
constant source. A compact full-W0 difference test, genuine p-monotonicity
and actual Holder flux bounds turn a actual scalar Lp gap into an Lp gradient
energy bound. The local geometric constant is chosen before either field.
No gradient closeness, energy conclusion, or classical regularity is input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem next_integral_norm_power
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p : ℝ} {μ : Measure X} {g : X → E}
    (hp : 1<p) (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫ x,‖g x‖^p ∂μ)=(eLpNorm g (ENNReal.ofReal p) μ).toReal^p := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have ht := BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp) (hg.toLp g)
  rw [Lp.norm_toLp] at ht
  have he := integral_congr_ae (hg.coeFn_toLp.fun_comp (fun v => ‖v‖^p))
  exact (ht.trans he).symm

private theorem next_gap_flux_holder
    {n : ℕ} {p : ℝ} {μ : Measure (Space n)}
    {f : Space n → ℝ} {g : Space n → Space n}
    (hp : 1<p) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal p) μ) :
    Integrable (fun x => ‖f x‖*‖pFlux p (g x)‖) μ ∧
    (∫ x,‖f x‖*‖pFlux p (g x)‖ ∂μ)≤
      (eLpNorm f (ENNReal.ofReal p) μ).toReal*
      (eLpNorm g (ENNReal.ofReal p) μ).toReal^(p-1) := by
  let q : ℝ := p/(p-1)
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  letI : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) := hpq.ennrealOfReal
  have hF : MemLp (fun x => ‖pFlux p (g x)‖) (ENNReal.ofReal q) μ := (memLp_pFlux hp hg).norm
  have hI : Integrable (fun x => ‖f x‖*‖pFlux p (g x)‖) μ := by
    simpa only [Pi.mul_apply] using! hf.norm.integrable_mul hF
  refine ⟨hI,?_⟩
  have hH := integral_mul_norm_le_Lp_mul_Lq hpq hf hF
  simp only [norm_norm] at hH
  have hfp := next_integral_norm_power hp hf
  have hgp : (∫ x,‖pFlux p (g x)‖^q ∂μ)=
      (eLpNorm g (ENNReal.ofReal p) μ).toReal^p := by
    simpa only [q,norm_pFlux_dual_power hp] using next_integral_norm_power hp hg
  rw [hfp,hgp,←Real.rpow_mul ENNReal.toReal_nonneg,
    ←Real.rpow_mul ENNReal.toReal_nonneg] at hH
  have he1 : p*(1/p)=1 := by field_simp
  have he2 : p*(1/q)=p-1 := by dsimp only [q];field_simp
  simpa only [he1,he2,Real.rpow_one] using hH

set_option maxHeartbeats 1800000 in
/-- Fixed local geometry supplies a genuine Lp weak-gradient stability
constant before both actual weak solutions and their actual scalar Lp gap.
The source is the same arbitrary real constant for both fields. -/
theorem exists_local_gradient_stability_constant_of_scalar_Lp_gap
    {n : ℕ} {p : ℝ} (hp : 2≤p) {U D : Set (Space n)}
    (hU : IsOpen U) (hD : LocalDomain D U) :
    ∃ C : ℝ,0≤C ∧ ∀ (c : ℝ) (u v : Space n → ℝ) (g h : Space n → Space n),
      WeakPSourcePair p c U u g → WeakPSourcePair p c U v h →
      SobolevPair p U u g → SobolevPair p U v h →
        Integrable (fun x => ‖g x-h x‖^p) (volume.restrict D) ∧
        (∫ x in D,‖g x-h x‖^p)≤C*
          (eLpNorm (u-v) (ENNReal.ofReal p) (volume.restrict U)).toReal*
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
  let α : ℝ := (1/2:ℝ)^p
  have hα : 0<α := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<1/2) _
  let C : ℝ := (p*P*2)/(4*α)
  refine ⟨C,div_nonneg (by positivity) (by positivity),?_⟩
  intro c u v g h hu hv su sv
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
  have hgapU := su.2.1.sub sv.2.1
  have hgapV := hgapU.mono_measure (Measure.restrict_mono_set volume hVU)
  obtain ⟨hFgI,hFg⟩ := next_gap_flux_holder hp1 hgapV hgV
  obtain ⟨hFhI,hFh⟩ := next_gap_flux_holder hp1 hgapV hhV
  let δ := (eLpNorm (u-v) (ENNReal.ofReal p) (volume.restrict U)).toReal
  have hδ : 0≤δ := ENNReal.toReal_nonneg
  have hgapN : (eLpNorm (u-v) (ENNReal.ofReal p) (volume.restrict V)).toReal≤δ :=
    ENNReal.toReal_mono hgapU.eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hVU))
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
  have hflux : (∫ x in V,‖(u-v) x‖*‖pFlux p (g x)‖)+
      (∫ x in V,‖(u-v) x‖*‖pFlux p (h x)‖)≤2*δ*S^(p-1) := by
    have hgPow := Real.rpow_le_rpow ENNReal.toReal_nonneg hNg (by linarith : 0≤p-1)
    have hhPow := Real.rpow_le_rpow ENNReal.toReal_nonneg hNh (by linarith : 0≤p-1)
    have hgB := mul_le_mul hgapN hgPow (Real.rpow_nonneg ENNReal.toReal_nonneg _) hδ
    have hhB := mul_le_mul hgapN hhPow (Real.rpow_nonneg ENNReal.toReal_nonneg _) hδ
    calc
      _≤δ*S^(p-1)+δ*S^(p-1) := add_le_add (hFg.trans hgB) (hFh.trans hhB)
      _=2*δ*S^(p-1) := by ring
  obtain ⟨-,hcrossI,-⟩ := hu.local_flux_difference_identity hv hV hχ
  have hcross := integral_mono_ae hcrossI.neg ((hFgI.add hFhI).const_mul P) (by
    filter_upwards [ae_restrict_mem hV.1.measurableSet] with x hx
    change -((u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x))≤
      P*(‖u x-v x‖*‖pFlux p (g x)‖+‖u x-v x‖*‖pFlux p (h x)‖)
    calc
      _≤|(u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)| := neg_le_abs _
      _=‖u x-v x‖ * |inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)| := by
        rw [abs_mul,Real.norm_eq_abs]
      _≤‖u x-v x‖*(‖pFlux p (g x)-pFlux p (h x)‖*‖gradient χ x‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (norm_nonneg _)
      _≤‖u x-v x‖*((‖pFlux p (g x)‖+‖pFlux p (h x)‖)*P) := mul_le_mul_of_nonneg_left
        (mul_le_mul (norm_sub_le _ _) (hPx x) (norm_nonneg _)
          (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _)
      _=_ := by ring)
  change (∫ x in V,-((u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)))≤
    ∫ x in V,P*(‖(u-v) x‖*‖pFlux p (g x)‖+‖(u-v) x‖*‖pFlux p (h x)‖) at hcross
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
  have hEc : (4*α)*(∫ x in D,‖g x-h x‖^p)≤p*(P*(2*δ*S^(p-1))) := by
    calc
      _≤(4*α)*(∫ x in V,χ x*‖g x-h x‖^p) := mul_le_mul_of_nonneg_left hdom (by positivity)
      _=4*(α*(∫ x in V,χ x*‖g x-h x‖^p)) := by ring
      _≤-p*(∫ x in V,(u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x)) := henergy
      _=p*(-(∫ x in V,(u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x))) := by ring
      _≤p*(P*((∫ x in V,‖(u-v) x‖*‖pFlux p (g x)‖)+(∫ x in V,‖(u-v) x‖*‖pFlux p (h x)‖))) := mul_le_mul_of_nonneg_left hcross hp0.le
      _≤_ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hflux hP.le) hp0.le
  have hden : 0<4*α := by positivity
  calc
    (∫ x in D,‖g x-h x‖^p)≤(p*(P*(2*δ*S^(p-1))))/(4*α) :=
      (le_div_iff₀ hden).mpr (by nlinarith only [hEc])
    _=C*δ*S^(p-1) := by dsimp only [C];ring

end BMCompactPDE
#print axioms BMCompactPDE.exists_local_gradient_stability_constant_of_scalar_Lp_gap
