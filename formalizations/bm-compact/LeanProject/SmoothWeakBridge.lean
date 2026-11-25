import WeakPDE
import CapacityFoundation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
The classical-to-distributional bridge.  Smooth functions have their actual
classical gradient as a weak gradient; this is proved by integration by parts,
including the compact-support argument which removes the domain boundary.
Consequently the smooth compact-support functions in the manuscript really
belong to the W^{1,p}_0 graph used by WeakPDE, with constant approximants.
-/

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace BMCompactPDE

theorem gradient_coordinate_eq_fderiv {n : ℕ} (u : Space n → ℝ)
    (x : Space n) (i : Fin n) :
    (gradient u x) i = fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  rw [← EuclideanSpace.inner_basisFun_real, inner_gradient_left]

/-- The test class in the weak derivative definition has genuine smooth
integration by parts, with no differentiability assumption on arbitrary
Sobolev representatives. -/
theorem hasWeakGradientOn_of_contDiff {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (Ω : Set (Space n)) :
    HasWeakGradientOn Ω u (gradient u) := by
  intro φ hφ i
  let v : Space n := EuclideanSpace.basisFun (Fin n) ℝ i
  have hdu : Continuous (fun x => fderiv ℝ u x v) :=
    (hu.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.1.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hφd : HasCompactSupport (fun x => fderiv ℝ φ x v) :=
    hφ.2.1.fderiv_apply ℝ v
  have h₁ : Integrable (fun x => u x * fderiv ℝ φ x v) volume :=
    (hu.continuous.mul hdφ).integrable_of_hasCompactSupport hφd.mul_left
  have h₂ : Integrable (fun x => fderiv ℝ u x v * φ x) volume :=
    (hdu.mul hφ.1.continuous).integrable_of_hasCompactSupport hφ.2.1.mul_left
  have h₃ : Integrable (fun x => u x * φ x) volume :=
    (hu.continuous.mul hφ.1.continuous).integrable_of_hasCompactSupport hφ.2.1.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    h₂ h₁ h₃ (fun x _ => hu.differentiable (by simp) x)
      (fun x _ => hφ.1.differentiable (by simp) x)
  have hφzero : ∀ x, x ∉ Ω → φ x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun ht => hx (hφ.2.2 ht))
  have hdφzero : ∀ x, x ∉ Ω → fderiv ℝ φ x v = 0 := by
    intro x hx
    have hx' : x ∉ tsupport (fun y => fderiv ℝ φ y v) :=
      fun ht => hx (hφ.2.2 ((tsupport_fderiv_apply_subset ℝ v) ht))
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y : Space n => fderiv ℝ φ y v) hx'
  have hleft : (∫ x in Ω, u x * fderiv ℝ φ x v) =
      ∫ x, u x * fderiv ℝ φ x v :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx
      simp [hdφzero x hx])
  have hright : (∫ x in Ω, fderiv ℝ u x v * φ x) =
      ∫ x, fderiv ℝ u x v * φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx
      simp [hφzero x hx])
  simp only [gradient_coordinate_eq_fderiv]
  exact ⟨h₁.restrict, h₂.restrict, by rw [hleft, hright]; exact hibp⟩

theorem SmoothTest.sobolevPair {n : ℕ} {p : ℝ} (hp : 1 < p)
    {D : Set (Space n)} {u : Space n → ℝ} (hu : SmoothTest D u) :
    SobolevPair p D u (gradient u) := by
  exact ⟨hp,
    (BMCompactCapacityV2.smooth_compactSupport_memLp (ENNReal.ofReal p) hu.1 hu.2.1).restrict D,
    (BMCompactCapacityV2.gradient_smooth_compactSupport_memLp
      (ENNReal.ofReal p) hu.1 hu.2.1).restrict D,
    hasWeakGradientOn_of_contDiff hu.1 D⟩

/-- A smooth compact-support test belongs to W^{1,p}_0 by the constant
approximating sequence, both in the function and in the gradient component. -/
theorem SmoothTest.zeroBoundarySobolevPair {n : ℕ} {p : ℝ} (hp : 1 < p)
    {D : Set (Space n)} {u : Space n → ℝ} (hu : SmoothTest D u) :
    ZeroBoundarySobolevPair p D u (gradient u) := by
  refine ⟨hu.sobolevPair hp, ⟨fun _ => u, fun _ => hu, ?_, ?_⟩⟩
  · simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  · simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

/-- On every nonempty open domain the test/Sobolev graph has a nonzero member.
This also records explicitly that the C∞ test class is not vacuous. -/
theorem exists_nonzero_zeroBoundarySobolevPair {n : ℕ} {p : ℝ} (hp : 1 < p)
    {D : Set (Space n)} (hD : IsOpen D) {x : Space n} (hx : x ∈ D) :
    ∃ u : Space n → ℝ, SmoothTest D u ∧
      ZeroBoundarySobolevPair p D u (gradient u) ∧ 1 ≤ u x ∧ u ≠ 0 := by
  obtain ⟨u, hu⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact
    (isCompact_singleton (x := x)) hD (singleton_subset_iff.mpr hx)
  have htest : SmoothTest D u := ⟨hu.1, hu.2.1, hu.2.2.1⟩
  have hone : 1 ≤ u x := hu.2.2.2 x (mem_singleton x)
  refine ⟨u, htest, htest.zeroBoundarySobolevPair hp, hone, ?_⟩
  intro hzero
  have hbad : (1 : ℝ) ≤ 0 := by simpa only [hzero, Pi.zero_apply] using hone
  exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) hbad

theorem sobolevPair_const {n : ℕ} {p : ℝ} (hp : 1 < p)
    {D : Set (Space n)} (hD : Bornology.IsBounded D) (c : ℝ) :
    SobolevPair p D (fun _ => c) 0 := by
  haveI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hD.measure_lt_top.ne
  refine ⟨hp, memLp_const c, MemLp.zero, ?_⟩
  simpa only [gradient_fun_const', Pi.zero_def] using hasWeakGradientOn_of_contDiff
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space n => c)) D

theorem weakPHarmonicPair_const {n : ℕ} {p : ℝ} (hp : 1 < p)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (c : ℝ) :
    WeakPHarmonicPair p Ω (fun _ => c) 0 := by
  refine ⟨hp, hΩ, fun D hD => sobolevPair_const hp hD.2.1 c, ?_⟩
  intro D _ θ h _
  have hzero : fluxPairing p (0 : Space n → Space n) h = 0 := by
    funext x
    simp [fluxPairing]
  rw [hzero]
  simp

theorem isWeakPHarmonic_const {n : ℕ} {p : ℝ} (hp : 1 < p)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (c : ℝ) :
    IsWeakPHarmonic p Ω (fun _ => c) :=
  ⟨0, weakPHarmonicPair_const hp hΩ c⟩


end BMCompactPDE

#print axioms BMCompactPDE.hasWeakGradientOn_of_contDiff
#print axioms BMCompactPDE.SmoothTest.sobolevPair
#print axioms BMCompactPDE.SmoothTest.zeroBoundarySobolevPair
#print axioms BMCompactPDE.exists_nonzero_zeroBoundarySobolevPair
#print axioms BMCompactPDE.sobolevPair_const
#print axioms BMCompactPDE.isWeakPHarmonic_const
