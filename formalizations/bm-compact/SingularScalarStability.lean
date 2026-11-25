import SingularDifferenceStability
import UpstreamGreenLocalGradientBound

/-! Interior stability for singular p-harmonic gradients, using only a
common bound and uniform difference of the two scalars. The cutoff and flux
L¹ estimate are adapted from UpstreamGreenLocalStability, and the integral
norm identity from CapacityNaturalHolder. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem singular_integral_norm_power {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ} (hp : 0<p)
    {z : α → E} (hz : MemLp z (ENNReal.ofReal p) μ) :
    ∫ x,‖z x‖^p ∂μ=(eLpNorm z (ENNReal.ofReal p) μ).toReal^p := by
  have hI : 0≤∫ x,‖z x‖^p ∂μ := integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  rw [hz.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp.le]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)]
  exact (Real.rpow_inv_rpow hI hp.ne').symm

private theorem singular_flux_L1_bound
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
    simpa only [q,norm_pFlux_dual_power hp] using singular_integral_norm_power (zero_lt_one.trans hp) hg
  rw [hpower,←Real.rpow_mul ENNReal.toReal_nonneg] at hH
  have he : p*(1/q)=p-1 := by
    dsimp only [q]
    field_simp
  rw [he] at hH
  simpa only [mul_comm] using hH

/-- For a prescribed scalar bound B, every two actual p-harmonic pairs
in the singular range obey an interior gradient-energy estimate C δ^(p/2)
where δ bounds their scalar difference. C is chosen before the fields. -/
theorem exists_local_singular_gradient_stability_of_scalar_bounds
    {n : ℕ} {p : ℝ} (hp : 1<p) (hp2 : p<2) {U D : Set (Space n)}
    (hU : IsOpen U) (hD : LocalDomain D U) {B : ℝ} (hB : 0≤B) :
    ∃ C : ℝ, 0≤C ∧ ∀ (u v : Space n → ℝ) (g h : Space n → Space n),
      WeakPHarmonicPair p U u g → WeakPHarmonicPair p U v h →
      (∀ x∈U, |u x|≤B) → (∀ x∈U, |v x|≤B) →
      ∀ δ : ℝ, 0≤δ → (∀ x∈U, |u x-v x|≤δ) →
        Integrable (fun x => ‖g x-h x‖^p) (volume.restrict D) ∧
        (∫ x in D, ‖g x-h x‖^p) ≤ C * δ^(p/2) := by
  have hp0 := zero_lt_one.trans hp
  have halpha : 0 < p/2 := by linarith
  have hb : 0 < 1-p/2 := by linarith
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
  let χ : Space n → ℝ := η
  have hχ : SmoothTest V χ := hη
  have hχ0 (x : Space n) : 0≤χ x := Real.smoothTransition.nonneg _
  have hχle (x : Space n) : χ x ≤ 1 := Real.smoothTransition.le_one _
  have hχ1 (x : Space n) (hx : x∈D) : χ x=1 := by
    have hη1 : η x=1 := Real.smoothTransition.one_of_one_le (ha.2.2.2 x (subset_closure hx))
    exact hη1
  have hgc : Continuous (gradient χ) := continuous_gradient_of_contDiff_one (hχ.1.of_le (by simp))
  obtain ⟨P,hP,hPb⟩ := ((BMCompactCapacityV2.gradient_hasCompactSupport hχ.2.1).isCompact_range hgc).isBounded.exists_pos_norm_le
  have hPx (x : Space n) : ‖gradient χ x‖≤P := hPb _ (mem_range_self x)
  let A : ℝ := (volume.real V)^(1/p)
  obtain ⟨Cg, hCg, hGb⟩ := exists_local_gradient_norm_bound_of_scalar_bound hp hU hV
  let M := Cg*B
  let F := 2*A*M^(p-1)
  let E := (2*M)^p
  let den := (p-1)^(p/2)
  have hA : 0≤A := Real.rpow_nonneg measureReal_nonneg _
  have hM : 0≤M := mul_nonneg hCg hB
  have hF : 0≤F := mul_nonneg (by positivity) (Real.rpow_nonneg hM _)
  have hE : 0≤E := Real.rpow_nonneg (by positivity) _
  have hden : 0<den := Real.rpow_pos_of_pos (sub_pos.mpr hp) _
  let C := ((P*F)^(p/2)*E^(1-p/2))/den
  refine ⟨C,div_nonneg (mul_nonneg (Real.rpow_nonneg (mul_nonneg hP.le hF) _) (Real.rpow_nonneg hE _)) hden.le,?_⟩
  intro u v g h hu hv hub hvb δ hδ hgap
  let : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hV.2.1.measure_lt_top.ne
  have hgV := (hu.2.2.1 V hV).2.2.1
  have hhV := (hv.2.2.1 V hV).2.2.1
  have hNg := hGb u g hu B hB hub
  have hNh := hGb v h hv B hB hvb
  have hNI : Integrable (fun x => ‖g x-h x‖^p) (volume.restrict V) := by
    simpa only [Pi.sub_apply] using integrable_norm_rpow_of_memLp hp (hgV.sub hhV)
  obtain ⟨hLI,hSI,henergy⟩ := hu.source_zero.local_unweighted_gradient_difference_singular
    hv.source_zero hp2 hV hχ hχ0
  have hID := hNI.mono_measure (Measure.restrict_mono_set volume hDV)
  have hdom : (∫ x in D,‖g x-h x‖^p)≤∫ x in V,χ x*‖g x-h x‖^p := by
    calc
      _=∫ x in D,χ x*‖g x-h x‖^p := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
        rw [hχ1 x hx,one_mul]
      _≤_ := integral_mono_measure (Measure.restrict_mono_set volume hDV)
        (Eventually.of_forall (fun x => mul_nonneg (hχ0 x) (Real.rpow_nonneg (norm_nonneg _) _))) hLI
  obtain ⟨hFgI,hFg⟩ := singular_flux_L1_bound hp hgV
  obtain ⟨hFhI,hFh⟩ := singular_flux_L1_bound hp hhV
  have hflux : (∫ x in V,‖pFlux p (g x)‖)+(∫ x in V,‖pFlux p (h x)‖)≤2*A*M^(p-1) := by
    have hgPow := Real.rpow_le_rpow ENNReal.toReal_nonneg hNg (by linarith : 0≤p-1)
    have hhPow := Real.rpow_le_rpow ENNReal.toReal_nonneg hNh (by linarith : 0≤p-1)
    have hgB : (∫ x in V,‖pFlux p (g x)‖)≤A*(eLpNorm g (ENNReal.ofReal p) (volume.restrict V)).toReal^(p-1) := by
      simpa only [A,Measure.real,Measure.restrict_apply_univ] using hFg
    have hhB : (∫ x in V,‖pFlux p (h x)‖)≤A*(eLpNorm h (ENNReal.ofReal p) (volume.restrict V)).toReal^(p-1) := by
      simpa only [A,Measure.real,Measure.restrict_apply_univ] using hFh
    calc
      _≤A*(eLpNorm g (ENNReal.ofReal p) (volume.restrict V)).toReal^(p-1)+
          A*(eLpNorm h (ENNReal.ofReal p) (volume.restrict V)).toReal^(p-1) := add_le_add hgB hhB
      _≤A*M^(p-1)+A*M^(p-1) := add_le_add
        (mul_le_mul_of_nonneg_left hgPow hA) (mul_le_mul_of_nonneg_left hhPow hA)
      _=2*A*M^(p-1) := by ring
  obtain ⟨-,hcrossI,-⟩ := hu.source_zero.local_flux_difference_identity hv.source_zero hV hχ
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
  let Z := -(∫ x in V,(u x-v x)*inner ℝ (pFlux p (g x)-pFlux p (h x)) (gradient χ x))
  have hZ0 : 0 ≤ Z := by
    have hw := (hu.source_zero.local_weighted_gradient_difference_bound hv.source_zero hp2.le hV hχ hχ0).2
    exact (integral_nonneg (fun x => mul_nonneg (hχ0 x) (mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hp.le) (Real.rpow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) _)) (sq_nonneg _)))).trans hw
  have hZ : Z ≤ δ*(P*F) := (hcross.trans (mul_le_mul_of_nonneg_left hflux (mul_nonneg hδ hP.le))).trans_eq (by dsimp only [F]; ring)
  let S := fun x => ‖g x‖+‖h x‖
  have hs : MemLp S (ENNReal.ofReal p) (volume.restrict V) := hgV.norm.add hhV.norm
  have hs0 (x) : 0≤S x := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsn : (eLpNorm S (ENNReal.ofReal p) (volume.restrict V)).toReal ≤ 2*M := by
    have hsN := eLpNorm_add_le hgV.norm.1 hhV.norm.1 (ENNReal.one_le_ofReal.mpr hp.le)
    have he := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hgV.norm.eLpNorm_ne_top,hhV.norm.eLpNorm_ne_top⟩) hsN
    rw [ENNReal.toReal_add hgV.norm.eLpNorm_ne_top hhV.norm.eLpNorm_ne_top, eLpNorm_norm,eLpNorm_norm] at he
    exact he.trans ((add_le_add hNg hNh).trans_eq (by dsimp only [M]; ring))
  have hsI : Integrable (fun x=>S x^p) (volume.restrict V) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hs0 _), ENNReal.toReal_ofReal hp0.le] using
      hs.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hmass : (∫ x in V, χ x * S x^p) ≤ E := by
    calc
      _ ≤ ∫ x in V, S x^p := integral_mono hSI hsI (fun x =>
        (mul_le_mul_of_nonneg_right (hχle x) (Real.rpow_nonneg (hs0 x) _)).trans_eq (one_mul _))
      _ = (eLpNorm S (ENNReal.ofReal p) (volume.restrict V)).toReal^p := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hs0 _)] using singular_integral_norm_power hp0 hs
      _ ≤ E := Real.rpow_le_rpow ENNReal.toReal_nonneg hsn hp0.le
  have hmass0 : 0 ≤ ∫ x in V, χ x * S x^p := integral_nonneg (fun x=>mul_nonneg (hχ0 x) (Real.rpow_nonneg (hs0 x) _))
  have hfinal : den*(∫ x in D,‖g x-h x‖^p) ≤ (δ*(P*F))^(p/2)*E^(1-p/2) :=
    ((mul_le_mul_of_nonneg_left hdom hden.le).trans henergy).trans
      (mul_le_mul (Real.rpow_le_rpow hZ0 hZ halpha.le) (Real.rpow_le_rpow hmass0 hmass hb.le)
        (Real.rpow_nonneg hmass0 _) (Real.rpow_nonneg (mul_nonneg hδ (mul_nonneg hP.le hF)) _))
  refine ⟨hID, ?_⟩
  have hquot := (le_div_iff₀ hden).2 ((mul_comm _ _).trans_le hfinal)
  apply hquot.trans_eq
  rw [Real.mul_rpow hδ (mul_nonneg hP.le hF)]
  dsimp only [C]
  ring

end BMCompactPDE
#print axioms BMCompactPDE.exists_local_singular_gradient_stability_of_scalar_bounds
