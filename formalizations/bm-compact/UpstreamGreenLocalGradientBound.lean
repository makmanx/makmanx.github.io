import GradientAnalyticBatch
import RegCaccioppoliInteger

/-! Actual local gradient Lp norm ceilings derived from a scalar uniform
ceiling for genuine homogeneous weak solutions. A single cutoff/collar and
integer exponent are chosen before the solution. The actual compact W0
Caccioppoli test supplies the estimate; no gradient norm or energy ceiling
is a premise. This is an Lp norm bound, not a pointwise gradient bound. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem green_bound_integral_norm_power
    {n : ℕ} {p : ℝ} {μ : Measure (Space n)} {g : Space n → Space n}
    (hp : 1<p) (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫ x,‖g x‖^p ∂μ)=(eLpNorm g (ENNReal.ofReal p) μ).toReal^p := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have ht := BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp) (hg.toLp g)
  rw [Lp.norm_toLp] at ht
  have he := integral_congr_ae (hg.coeFn_toLp.fun_comp (fun v => ‖v‖^p))
  exact (ht.trans he).symm

set_option maxHeartbeats 1600000 in
/-- The actual homogeneous weak PDE derives one local gradient-Lp coefficient
before the scalar and gradient fields, from a scalar uniform bound alone. -/
theorem exists_local_gradient_norm_bound_of_scalar_bound
    {n : ℕ} {p : ℝ} (hp : 1<p) {U D : Set (Space n)}
    (hU : IsOpen U) (hD : LocalDomain D U) :
    ∃ C : ℝ,0≤C ∧ ∀ (u : Space n → ℝ) (g : Space n → Space n),
      WeakPHarmonicPair p U u g → ∀ B : ℝ,0≤B → (∀ x∈U,|u x|≤B) →
        (eLpNorm g (ENNReal.ofReal p) (volume.restrict D)).toReal≤C*B := by
  have hp0 : 0<p := zero_lt_one.trans hp
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
  have hη0 (x : Space n) : 0≤η x := Real.smoothTransition.nonneg _
  have hηle (x : Space n) : η x≤1 := Real.smoothTransition.le_one _
  have hη1 (x : Space n) (hx : x∈D) : η x=1 :=
    Real.smoothTransition.one_of_one_le (ha.2.2.2 x (subset_closure hx))
  have hgc : Continuous (gradient η) := continuous_gradient_of_contDiff_one (hη.1.of_le (by simp))
  obtain ⟨P,hP,hPb⟩ := ((BMCompactCapacityV2.gradient_hasCompactSupport hη.2.1).isCompact_range hgc).isBounded.exists_pos_norm_le
  have hPx (x : Space n) : ‖gradient η x‖≤P := hPb _ (mem_range_self x)
  let M : ℕ := ⌈p⌉₊
  have hM : p≤(M:ℝ) := Nat.le_ceil p
  let E : ℝ := (M:ℝ)^p*P^p*volume.real V
  have hE : 0≤E := by dsimp only [E];positivity
  let C : ℝ := E^(1/p)
  have hC : 0≤C := Real.rpow_nonneg hE _
  refine ⟨C,hC,?_⟩
  intro u g hu B hB hbound
  have hSobV := hu.2.2.1 V hV
  have hGraw := integrable_norm_rpow_of_memLp hp hSobV.2.2.1
  have hGI : Integrable (fun x => ‖g x‖^p) (volume.restrict V) := hGraw
  have hM0 : M≠0 := by
    intro hz
    have hm := hM
    rw [hz,Nat.cast_zero] at hm
    linarith
  have hpow := hη.natPow_cutoff hM0
  have hηpow : MemLp (fun x => η x^M) (∞:ℝ≥0∞) (volume.restrict V) :=
    hpow.1.continuous.memLp_top_of_hasCompactSupport hpow.2.1 _
  have hLI : Integrable (fun x => η x^M*‖g x‖^p) (volume.restrict V) := by
    simpa only [Pi.mul_apply,mul_comm] using! hGI.mul_of_top_right hηpow
  have hdom : (∫ x in D,‖g x‖^p)≤∫ x in V,η x^M*‖g x‖^p := by
    calc
      _=∫ x in D,η x^M*‖g x‖^p := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
        rw [hη1 x hx,one_pow,one_mul]
      _≤_ := integral_mono_measure (Measure.restrict_mono_set volume hDV)
        (Eventually.of_forall (fun x => mul_nonneg (pow_nonneg (hη0 x) _)
          (Real.rpow_nonneg (norm_nonneg _) _))) hLI
  have huI : Integrable (fun x => |u x|^p) (volume.restrict V) := by
    simpa only [ENNReal.toReal_ofReal hp0.le,Real.norm_eq_abs] using
      hSobV.2.1.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hgradp : Continuous (fun x => ‖gradient η x‖^p) :=
    hgc.norm.rpow_const (fun _ => Or.inr hp0.le)
  have hRI : Integrable (fun x => |u x|^p*‖gradient η x‖^p) (volume.restrict V) := by
    apply (huI.mul_const (P^p)).mono_nonneg (huI.1.mul hgradp.aestronglyMeasurable)
    · exact Eventually.of_forall (fun x => mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
        (Real.rpow_nonneg (norm_nonneg _) _))
    · exact Eventually.of_forall (fun x => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (hPx x) hp0.le)
        (Real.rpow_nonneg (abs_nonneg _) _))
  letI : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hV.2.1.measure_lt_top.ne
  have hRbound : (∫ x in V,|u x|^p*‖gradient η x‖^p)≤volume.real V*(B^p*P^p) := by
    have hi := integral_mono_ae hRI (integrable_const (B^p*P^p)) (by
      filter_upwards [ae_restrict_mem hV.1.measurableSet] with x hx
      exact mul_le_mul
        (Real.rpow_le_rpow (abs_nonneg _) (hbound x (hVU hx)) hp0.le)
        (Real.rpow_le_rpow (norm_nonneg _) (hPx x) hp0.le)
        (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hB _))
    simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] using hi
  have he := hu.caccioppoli_natPow (M:=M) hV hη hη0 hηle hM 0
  simp only [sub_zero] at he
  have henergy : (∫ x in D,‖g x‖^p)≤E*B^p := by
    calc
      _≤(M:ℝ)^p*(∫ x in V,|u x|^p*‖gradient η x‖^p) := hdom.trans he
      _≤(M:ℝ)^p*(volume.real V*(B^p*P^p)) :=
        mul_le_mul_of_nonneg_left hRbound (Real.rpow_nonneg (Nat.cast_nonneg M) _)
      _=E*B^p := by dsimp only [E];ring
  have hgp := (hu.2.2.1 D hD).2.2.1
  rw [green_bound_integral_norm_power hp hgp] at henergy
  apply (Real.rpow_le_rpow_iff ENNReal.toReal_nonneg (mul_nonneg hC hB) hp0).mp
  have hCP : (C*B)^p=E*B^p := by
    rw [Real.mul_rpow hC hB]
    dsimp only [C]
    rw [one_div,Real.rpow_inv_rpow hE hp0.ne']
  rw [hCP]
  exact henergy

end BMCompactPDE
#print axioms BMCompactPDE.exists_local_gradient_norm_bound_of_scalar_bound
