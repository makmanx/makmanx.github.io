import UpstreamMorreyRepresentative
import RootSobolevLocalization
import ComparisonQuantitativeCutoff

/-! Uniform local Morrey control for actual continuous Sobolev families above
the dimension. A single compact cutoff and its derivative bound are selected
before the scalar/gradient fields and their norm ceilings. The ceilings remain
explicit hypotheses; no claim that a constructed Green family satisfies them
is made in this module. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal NNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1200000 in
theorem exists_uniform_local_morrey_coefficient_for_continuous_sobolev_families
    {n : ℕ} {p : ℝ} {ι : Type*} (hn : 1≤n) (hnp : (n : ℝ)<p)
    {U D : Set (Space n)} (hU : IsOpen U) (hD : LocalDomain D U) :
    ∃ C : ℝ,0≤C ∧ ∀ M₀ M₁ : ℝ,0≤M₀ → 0≤M₁ →
      ∀ (u : ι → Space n → ℝ) (g : ι → Space n → Space n),
        (∀ j,SobolevPair p U (u j) (g j)) → (∀ j,ContinuousOn (u j) U) →
        (∀ j,(eLpNorm (u j) (ENNReal.ofReal p) (volume.restrict U)).toReal≤M₀) →
        (∀ j,(eLpNorm (g j) (ENNReal.ofReal p) (volume.restrict U)).toReal≤M₁) →
        ∀ j x,x∈closure D → ∀ y,y∈closure D →
          dist (u j x) (u j y)≤C*(M₀+M₁)*dist x y^(1-(n : ℝ)/p) := by
  obtain ⟨A,hA⟩ := exists_actual_global_morrey_constant hn hnp
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hU hD.2.2
  let χ : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp hf.1
  have hχc : HasCompactSupport χ := hf.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)))
  have hχs : tsupport χ⊆U :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1
  have hχ0 (x : Space n) : 0≤χ x := Real.smoothTransition.nonneg _
  have hχle (x : Space n) : χ x≤1 := Real.smoothTransition.le_one _
  have hχ1 (x : Space n) (hx : x∈closure D) : χ x=1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)
  have hgc : Continuous (gradient χ) := continuous_gradient_of_contDiff_one (hχ.of_le (by simp))
  obtain ⟨P,hP,hPb⟩ := ((BMCompactCapacityV2.gradient_hasCompactSupport hχc).isCompact_range hgc).isBounded.exists_pos_norm_le
  have hPx (x : Space n) : ‖gradient χ x‖≤P := hPb _ (mem_range_self x)
  refine ⟨(A : ℝ)*(1+P),mul_nonneg A.coe_nonneg (by positivity),?_⟩
  intro M₀ M₁ hM₀ hM₁ u g hSob hcont hMscalar hMgradient j x hx y hy
  let q : ℝ≥0∞ := ENNReal.ofReal p
  let μ := volume.restrict U
  let F : Space n → ℝ := fun z => χ z*u j z
  let G₁ : Space n → Space n := fun z => χ z • g j z
  let G₂ : Space n → Space n := fun z => u j z • gradient χ z
  let H : Space n → Space n := fun z => G₁ z+G₂ z
  have hS : SobolevPair p univ F H :=
    (hSob j).mul_smooth_compactSupport_global hU hχ hχc hχs
  have hG₁bound (z : Space n) : ‖G₁ z‖≤‖g j z‖ := by
    change ‖χ z • g j z‖≤‖g j z‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hχ0 z)]
    exact (mul_le_mul_of_nonneg_right (hχle z) (norm_nonneg _)).trans_eq (one_mul _)
  have hG₂bound (z : Space n) : ‖G₂ z‖≤P*‖u j z‖ := by
    change ‖u j z • gradient χ z‖≤P*‖u j z‖
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (hPx z) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hG₁ : MemLp G₁ q μ := (hSob j).2.2.1.of_le
    (hχ.continuous.aestronglyMeasurable.smul (hSob j).2.2.1.1) (Eventually.of_forall hG₁bound)
  have hG₂ : MemLp G₂ q μ := (hSob j).2.1.of_le_mul
    ((hSob j).2.1.1.smul hgc.aestronglyMeasurable) (Eventually.of_forall hG₂bound)
  have hHzero (z : Space n) (hz : z∉U) : H z=0 := by
    have hzt : z∉tsupport χ := fun ht => hz (hχs ht)
    have hχz := image_eq_zero_of_notMem_tsupport hzt
    have hgχ := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport hzt
    simp only [H,G₁,G₂,hχz,hgχ,zero_smul,smul_zero,add_zero]
  have hHi : U.indicator H=H := by
    funext z
    by_cases hz : z∈U
    · exact indicator_of_mem hz H
    · simp only [indicator_of_notMem hz,hHzero z hz]
  have hHN : eLpNorm H q volume=eLpNorm H q μ := by
    calc
      _=eLpNorm (U.indicator H) q volume := by rw [hHi]
      _=_ := eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet
  have hG₁N : eLpNorm G₁ q μ≤eLpNorm (g j) q μ :=
    eLpNorm_mono_ae (Eventually.of_forall hG₁bound)
  have hG₂N : eLpNorm G₂ q μ≤ENNReal.ofReal P*eLpNorm (u j) q μ :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall hG₂bound) q
  have hsum : eLpNorm H q μ≤eLpNorm (g j) q μ+ENNReal.ofReal P*eLpNorm (u j) q μ :=
    (eLpNorm_add_le hG₁.1 hG₂.1 (ENNReal.one_le_ofReal.mpr (hSob j).1.le)).trans
      (add_le_add hG₁N hG₂N)
  have hgfinite : eLpNorm (g j) q μ≠(∞ : ℝ≥0∞) := (hSob j).2.2.1.eLpNorm_ne_top
  have hufinite : eLpNorm (u j) q μ≠(∞ : ℝ≥0∞) := (hSob j).2.1.eLpNorm_ne_top
  have hprod : ENNReal.ofReal P*eLpNorm (u j) q μ≠(∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hufinite
  have hnorm : (eLpNorm H q volume).toReal≤
      (eLpNorm (g j) q μ).toReal+P*(eLpNorm (u j) q μ).toReal := by
    rw [hHN]
    have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hgfinite,hprod⟩) hsum
    simpa only [ENNReal.toReal_add hgfinite hprod,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hP.le] using hh
  have hnorm' : (eLpNorm H q volume).toReal≤(1+P)*(M₀+M₁) := by
    calc
      _≤M₁+P*M₀ := hnorm.trans (add_le_add (hMgradient j)
        (mul_le_mul_of_nonneg_left (hMscalar j) hP.le))
      _≤_ := by nlinarith only [hM₀,mul_nonneg hP.le hM₁]
  obtain ⟨v,hvc,hFv,hv⟩ := hA F H hS
  have hFvc : ContinuousOn F U := hχ.continuous.continuousOn.mul (hcont j)
  have hFveq : EqOn F v U :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hFv) hU hFvc hvc.continuousOn
  have huv (z : Space n) (hz : z∈closure D) : u j z=v z := by
    simpa only [F,hχ1 z hz,one_mul] using hFveq (hD.2.2 hz)
  rw [huv x hx,huv y hy]
  calc
    _≤(A : ℝ)*(eLpNorm H q volume).toReal*dist x y^(1-(n : ℝ)/p) := hv x y
    _≤(A : ℝ)*((1+P)*(M₀+M₁))*dist x y^(1-(n : ℝ)/p) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm' A.coe_nonneg)
        (Real.rpow_nonneg dist_nonneg _)
    _=_ := by ring

end BMCompactPDE
#print axioms BMCompactPDE.exists_uniform_local_morrey_coefficient_for_continuous_sobolev_families
