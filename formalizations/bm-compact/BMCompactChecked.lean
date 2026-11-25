import Algebra
import Geometry
import ConeIteration
import FluxDefs
import GreenFoundation
import RadialFoundation
import FundamentalProfiles
import RadialDivergenceCore
import RadialDivergence
import RadialRegularity
import EuclideanDivergence
import CapacityFoundation
import CapacityOuterRegularity
import CapacityNeighborhood
import WeakPDE
import WeakSobolevAE
import WeakHarmonicScaling
import SmoothWeakBridge
import LocalSmoothWeakBridge
import WeakUniqueness
import WeakEnergyUniqueness
import WeakDensity
import WeakDivergence
import WeakClassicalDivergence
import OuterComparison
import GreenDefs
import RadialSobolev
import WeakAffine
import RadialFluxSmooth
import RadialWeakHarmonic
import RadialGlobalContinuity
import SingletonGreen
import BallGreenCore
import BallGreenExistence
import BallGreenCapacity
import BallGreenOrder
import RadialTranslationLimit
import RadialDilation
import TranslatedRadialWeak
import TranslatedBallWeak
import GreenAsymptoticBasics
import TranslatedBallGreen
import WeakPoincare
import WeakContinuousUniqueness
import WeakGlobalTesting
import WeakPositivePartComparison
import TheoremAOuterReduction
import CapacityAffineEnergy
import CapacityAffine
import RelativeCapacityAffine
import CapacityNormalization
import CapacityNormalizationFull
import SupConvolution
import SupConvolutionProperties
import SupConvolutionRadialTail
import SupConvolutionGreenTail
import TouchingLinear
import TouchingDerivative
import TouchingGradient
import TouchingSecondCalculus
import TouchingPLaplace
import LpDominatedLimit
import SmoothPositivePart
import SmoothPositivePartAdmissibility
import SmoothBoundaryComparison
import CondenserExtension
import CondenserExtensionAffine
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! V5 actual weak-PDE, viscosity and Hopf supporting foundations.
Main Theorems A, B and C remain unproved. Open targets are excluded.
New proof bodies are composed here once; segments are not separate build targets. -/

/-! Exact development proof segment: ViscosityDefs -/
section V5SegmentViscosityDefs

/-! Noncritical viscosity tests for the actual normalized p-Laplacian in
source Definition3.6/eqn3.8. The local non-strict test convention is stronger
than the manuscript's globally strict convention; the implication is proved
separately. No equivalence, comparison, or weak-PDE bridge is built into a def. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology ContDiff
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Standard local upper-test convention, ignoring zero-gradient tests as
in the manuscript. Every derivative is the actual Mathlib derivative. -/
def IsViscosityPSubsolution (p : ℝ) (Ω : Set E) (u : E → ℝ) : Prop :=
  1 < p ∧ IsOpen Ω ∧ UpperSemicontinuousOn u Ω ∧
    ∀ x ∈ Ω, ∀ φ : E → ℝ, ContDiffAt ℝ 2 φ x → u x = φ x →
      (∀ᶠ y in 𝓝 x, u y ≤ φ y) → gradient φ x ≠ 0 →
        0 ≤ normalizedPLaplacian p φ x

/-- Exact globally strict upper-test convention in source Definition3.6. -/
def IsManuscriptViscosityPSubsolution (p : ℝ) (Ω : Set E) (u : E → ℝ) : Prop :=
  1 < p ∧ IsOpen Ω ∧ UpperSemicontinuousOn u Ω ∧
    ∀ x ∈ Ω, ∀ φ : E → ℝ, ContDiffOn ℝ 2 φ Ω → u x = φ x →
      (∀ y ∈ Ω, y ≠ x → u y < φ y) → gradient φ x ≠ 0 →
        0 ≤ normalizedPLaplacian p φ x

end BMCompactAnalytic
end
end V5SegmentViscosityDefs


/-! Exact development proof segment: ClassicalFluxDerivative -/
section V5SegmentClassicalFluxDerivative

/-! Actual nonlinear flux differentiation and the genuine divergence/Hessian
identity, at noncritical locally C2 points. No weak/classical bridge is assumed. -/
noncomputable section
set_option autoImplicit false
open Filter Set InnerProductSpace
open scoped Topology ContDiff InnerProductSpace
namespace BMCompactPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hasFDerivAt_pFlux (p : ℝ) {v : E} (hv : v ≠ 0) :
    HasFDerivAt (pFlux p : E → E)
      (‖v‖ ^ (p-2) • ContinuousLinearMap.id ℝ E +
        (((p-2) * ‖v‖ ^ (p-4)) • innerSL ℝ v).smulRight v) v := by
  have h := hasFDerivAt_norm_rpow_smul (p-2) hv
  change HasFDerivAt (fun y : E => ‖y‖ ^ (p-2) • y) _ v
  simpa only [show p-2-2 = p-4 by ring] using! h

theorem contDiffAt_pFlux (p : ℝ) {v : E} (hv : v ≠ 0) :
    ContDiffAt ℝ ∞ (pFlux p : E → E) v := by
  have hnorm : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) v := contDiffAt_norm ℝ hv
  exact (hnorm.rpow_const_of_ne (norm_ne_zero_iff.mpr hv)).smul contDiffAt_id

theorem hasFDerivAt_pFlux_comp (p : ℝ) {g : E → E} {x : E}
    {D : E →L[ℝ] E} (hg : HasFDerivAt g D x) (hg0 : g x ≠ 0) :
    HasFDerivAt (fun y => pFlux p (g y))
      (‖g x‖ ^ (p-2) • D +
        ((((p-2) * ‖g x‖ ^ (p-4)) • innerSL ℝ (g x)).comp D).smulRight (g x)) x := by
  convert! (hasFDerivAt_pFlux p hg0).comp x hg using 1

section Finite
variable [FiniteDimensional ℝ E]

theorem classicalDivergence_pFlux_comp (p : ℝ) {g : E → E} {x : E}
    (hg : DifferentiableAt ℝ g x) (hg0 : g x ≠ 0) :
    classicalDivergence (fun y => pFlux p (g y)) x =
      ‖g x‖ ^ (p-2) * classicalDivergence g x +
        (p-2) * ‖g x‖ ^ (p-4) * inner ℝ (g x) (fderiv ℝ g x (g x)) := by
  unfold classicalDivergence
  rw [(hasFDerivAt_pFlux_comp p hg.hasFDerivAt hg0).fderiv]
  change LinearMap.trace ℝ E
    (‖g x‖ ^ (p-2) • (fderiv ℝ g x).toLinearMap +
      (((((p-2) * ‖g x‖ ^ (p-4)) • innerSL ℝ (g x)).comp
        (fderiv ℝ g x)).toLinearMap).smulRight (g x)) = _
  rw [map_add,map_smul,LinearMap.trace_smulRight]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    smul_apply, coe_innerSL_apply, smul_eq_mul]

end Finite
section Complete
variable [CompleteSpace E]

theorem hasFDerivAt_gradient_of_contDiffAt_two {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    HasFDerivAt (gradient u)
      ((toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ u) x)) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simpa only [gradient] using!
    (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x hd.hasFDerivAt

theorem fderiv_gradient_eq_actualHessianEnd {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    (fderiv ℝ (gradient u) x).toLinearMap = BMCompactAnalytic.actualHessianEnd u x := by
  rw [(hasFDerivAt_gradient_of_contDiffAt_two hu).fderiv]
  rfl

theorem inner_fderiv_gradient_eq_actualHessian {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (a b : E) :
    inner ℝ a (fderiv ℝ (gradient u) x b) = BMCompactAnalytic.actualHessian u x b a := by
  rw [(hasFDerivAt_gradient_of_contDiffAt_two hu).fderiv]
  change inner ℝ a ((toDual ℝ E).symm (BMCompactAnalytic.actualHessian u x b)) = _
  rw [real_inner_comm,←toDual_apply_apply,(toDual ℝ E).apply_symm_apply]

variable [FiniteDimensional ℝ E]

/-- The actual divergence of the actual nonlinear gradient flux is exactly
the source's Hessian-form classical p-Laplacian at every noncritical C2 point. -/
theorem classicalDivergence_pFlux_gradient_eq_classicalPLaplacian
    (p : ℝ) {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (hg : gradient u x ≠ 0) :
    classicalDivergence (fun y => pFlux p (gradient u y)) x =
      BMCompactAnalytic.classicalPLaplacian p u x := by
  rw [classicalDivergence_pFlux_comp p
    (hasFDerivAt_gradient_of_contDiffAt_two hu).differentiableAt hg,
    inner_fderiv_gradient_eq_actualHessian hu]
  have hdiv : classicalDivergence (gradient u) x = BMCompactAnalytic.actualLaplacian u x := by
    unfold classicalDivergence BMCompactAnalytic.actualLaplacian
    rw [fderiv_gradient_eq_actualHessianEnd hu]
  rw [hdiv]
  unfold BMCompactAnalytic.classicalPLaplacian BMCompactAnalytic.normalizedPLaplacian
  have hr : 0 < ‖gradient u x‖ := norm_pos_iff.mpr hg
  have hp : ‖gradient u x‖ ^ (p-4) =
      ‖gradient u x‖ ^ (p-2) * (‖gradient u x‖ ^ 2)⁻¹ := by
    rw [← Real.rpow_two,←Real.rpow_neg hr.le,←Real.rpow_add hr]
    congr 1
    ring
  rw [hp]
  ring

end Complete
end BMCompactPDE
end
end V5SegmentClassicalFluxDerivative


/-! Exact development proof segment: ClassicalPLaplaceBridge -/
section V5SegmentClassicalPLaplaceBridge

/-! Actual local integration by parts and local Sobolev membership need only
C1, not C-infinity. Smoothness of the test functions remains genuine C-infinity. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE
theorem hasWeakGradientOn_of_contDiffOn_one {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ 1 u Ω) :
    HasWeakGradientOn Ω u (gradient u) := by
  intro φ hφ i
  let v : Space n := EuclideanSpace.basisFun (Fin n) ℝ i
  have hdu : ContinuousOn (fun x => fderiv ℝ u x v) Ω :=
    (hu.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.1.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hφd : HasCompactSupport (fun x => fderiv ℝ φ x v) :=
    hφ.2.1.fderiv_apply ℝ v
  have hsupport₁ : tsupport (fun x => u x * fderiv ℝ φ x v) ⊆ Ω :=
    tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ v).trans hφ.2.2)
  have hsupport₂ : tsupport (fun x => fderiv ℝ u x v * φ x) ⊆ Ω :=
    tsupport_mul_subset_right.trans hφ.2.2
  have hsupport₃ : tsupport (fun x => u x * φ x) ⊆ Ω :=
    tsupport_mul_subset_right.trans hφ.2.2
  have hc₁ : Continuous (fun x => u x * fderiv ℝ φ x v) :=
    (hu.continuousOn.mul hdφ.continuousOn).continuous_of_tsupport_subset hΩ hsupport₁
  have hc₂ : Continuous (fun x => fderiv ℝ u x v * φ x) :=
    (hdu.mul hφ.1.continuous.continuousOn).continuous_of_tsupport_subset hΩ hsupport₂
  have hc₃ : Continuous (fun x => u x * φ x) :=
    (hu.continuousOn.mul hφ.1.continuous.continuousOn).continuous_of_tsupport_subset hΩ hsupport₃
  have h₁ : Integrable (fun x => u x * fderiv ℝ φ x v) volume :=
    hc₁.integrable_of_hasCompactSupport hφd.mul_left
  have h₂ : Integrable (fun x => fderiv ℝ u x v * φ x) volume :=
    hc₂.integrable_of_hasCompactSupport hφ.2.1.mul_left
  have h₃ : Integrable (fun x => u x * φ x) volume :=
    hc₃.integrable_of_hasCompactSupport hφ.2.1.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    h₂ h₁ h₃
    (fun x hx => (hu.contDiffAt (hΩ.mem_nhds (hφ.2.2 hx))).differentiableAt (by simp))
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

theorem continuousOn_gradient_of_contDiffOn_one {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ 1 u Ω) :
    ContinuousOn (gradient u) Ω := by
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.comp_continuousOn
    (hu.continuousOn_fderiv_of_isOpen hΩ (by simp))

/-- On each relatively compact bounded open test domain, locally smooth u
and its actual classical gradient form the manuscript's Sobolev pair. -/
theorem sobolevPair_of_contDiffOn_one {n : ℕ} {p : ℝ} (hp : 1 < p)
    {Ω D : Set (Space n)} (hΩ : IsOpen Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 1 u Ω) (hD : LocalDomain D Ω) :
    SobolevPair p D u (gradient u) := by
  have hDΩ : D ⊆ Ω := subset_closure.trans hD.2.2
  refine ⟨hp, ?_, ?_, ?_⟩
  · exact memLp_on_bounded_of_continuousOn_closure (ENNReal.ofReal p)
      hD.2.1 hD.1.measurableSet (hu.continuousOn.mono hD.2.2)
  · exact memLp_on_bounded_of_continuousOn_closure (ENNReal.ofReal p)
      hD.2.1 hD.1.measurableSet
      ((continuousOn_gradient_of_contDiffOn_one hΩ hu).mono hD.2.2)
  · exact hasWeakGradientOn_of_contDiffOn_one hD.1 (hu.mono hDΩ)

/-- Genuine local C1 functions have local W1p membership with their
actual classical gradient, in the concrete weak-gradient graph. -/
theorem locallySobolevPair_of_contDiffOn_one {n : ℕ} {p : ℝ} (hp : 1 < p)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 1 u Ω) :
    LocallySobolevPair p Ω u (gradient u) := by
  intro D hD
  exact sobolevPair_of_contDiffOn_one hp hΩ hu hD


end BMCompactPDE


/-! Actual C1 flux fields satisfy integration by parts and yield the complete
weak p-Laplace equation. No C-infinity extension of the flux is required. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff InnerProductSpace
namespace BMCompactPDE
theorem integral_inner_gradient_eq_neg_divergence_one {n : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {F : Space n → Space n}
    (hF : ∀ i : Fin n, ContDiffOn ℝ 1 (fun x => F x i) Ω)
    {φ : Space n → ℝ} (hφ : SmoothTest Ω φ) :
    Integrable (fun x => inner ℝ (F x) (gradient φ x)) (volume.restrict Ω) ∧
    Integrable (fun x => coordinateDivergence F x * φ x) (volume.restrict Ω) ∧
      (∫ x in Ω, inner ℝ (F x) (gradient φ x)) =
        -(∫ x in Ω, coordinateDivergence F x * φ x) := by
  let L : Fin n → Space n → ℝ := fun i x => F x i * (gradient φ x) i
  let R : Fin n → Space n → ℝ :=
    fun i x => (gradient (fun y => F y i) x) i * φ x
  have hcoord (i : Fin n) := hasWeakGradientOn_of_contDiffOn_one hΩ (hF i) φ hφ i
  have hLi (i : Fin n) : Integrable (L i) (volume.restrict Ω) := (hcoord i).1
  have hRi (i : Fin n) : Integrable (R i) (volume.restrict Ω) := (hcoord i).2.1
  have hL : Integrable (fun x => ∑ i : Fin n, L i x) (volume.restrict Ω) := by
    convert integrable_finsetSum Finset.univ (fun i _ => hLi i) using 1
  have hR : Integrable (fun x => ∑ i : Fin n, R i x) (volume.restrict Ω) := by
    convert integrable_finsetSum Finset.univ (fun i _ => hRi i) using 1
  have hinner : (fun x => inner ℝ (F x) (gradient φ x)) =
      (fun x => ∑ i : Fin n, L i x) := by
    funext x
    simp only [L, PiLp.inner_apply, Real.inner_apply]
  have hdiv : (fun x => coordinateDivergence F x * φ x) =
      (fun x => ∑ i : Fin n, R i x) := by
    funext x
    simp only [coordinateDivergence, Finset.sum_mul, R]
  refine ⟨?_, ?_, ?_⟩
  · rw [hinner]
    exact hL
  · rw [hdiv]
    exact hR
  · rw [hinner, hdiv, integral_finsetSum Finset.univ (fun i _ => hLi i),
      integral_finsetSum Finset.univ (fun i _ => hRi i)]
    calc
      (∑ i : Fin n, ∫ x in Ω, L i x) = ∑ i : Fin n, -(∫ x in Ω, R i x) :=
        Finset.sum_congr rfl (fun i _ => (hcoord i).2.2)
      _ = -(∑ i : Fin n, ∫ x in Ω, R i x) :=
        Finset.sum_neg_distrib (fun i : Fin n => ∫ x in Ω, R i x)

theorem integral_inner_gradient_eq_zero_of_divergence_eq_zero_one {n : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {F : Space n → Space n}
    (hF : ∀ i : Fin n, ContDiffOn ℝ 1 (fun x => F x i) Ω)
    (hdivF : ∀ x ∈ Ω, coordinateDivergence F x = 0)
    {φ : Space n → ℝ} (hφ : SmoothTest Ω φ) :
    (∫ x in Ω, inner ℝ (F x) (gradient φ x)) = 0 := by
  have hzero : (fun x => coordinateDivergence F x * φ x) = 0 := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hdivF x hx]
    · have hφx : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => hx (hφ.2.2 ht))
      simp [hφx]
  rw [(integral_inner_gradient_eq_neg_divergence_one hΩ hF hφ).2.2, hzero]
  simp

/-- A locally smooth, classically divergence-free actual p-flux satisfies
the manuscript's full Sobolev-test weak equation. -/
theorem weakPHarmonicPair_of_divergence_eq_zero_one {n : ℕ} {p : ℝ}
    (hp : 1 < p) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hSob : LocallySobolevPair p Ω u g)
    (hflux : ∀ i : Fin n, ContDiffOn ℝ 1 (fun x => pFlux p (g x) i) Ω)
    (hdiv : ∀ x ∈ Ω, coordinateDivergence (fun y => pFlux p (g y)) x = 0) :
    WeakPHarmonicPair p Ω u g := by
  apply weakPHarmonicPair_of_smooth_test_equation hp hΩ hSob
  intro D hD φ hφ
  have hDΩ : D ⊆ Ω := subset_closure.trans hD.2.2
  exact integral_inner_gradient_eq_zero_of_divergence_eq_zero_one hD.1
    (fun i => (hflux i).mono hDΩ) (fun x hx => hdiv x (hDΩ hx)) hφ


end BMCompactPDE


/-! Actual C2/noncritical weak-classical p-Laplace equivalence. Both the
local Sobolev graph and C1 flux integration by parts are derived. The reverse
direction uses Mathlib's genuine fundamental lemma of distributions. This
does not prove C2 regularity of an arbitrary weak solution. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff InnerProductSpace
namespace BMCompactPDE

theorem contDiffOn_gradient_of_contDiffOn_two {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u Ω) :
    ContDiffOn ℝ 1 (gradient u) Ω := by
  intro x hx
  have hd : ContDiffAt ℝ 1 (fderiv ℝ u) x :=
    (hu.contDiffAt (hΩ.mem_nhds hx)).fderiv_right (by norm_num)
  exact ((InnerProductSpace.toDual ℝ (Space n)).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp x hd).contDiffWithinAt

theorem contDiffOn_pFlux_gradient_of_contDiffOn_two {n : ℕ} (p : ℝ)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 2 u Ω) (hg : ∀ x ∈ Ω, gradient u x ≠ 0) :
    ContDiffOn ℝ 1 (fun x => pFlux p (gradient u x)) Ω := by
  have hgrad := contDiffOn_gradient_of_contDiffOn_two hΩ hu
  intro x hx
  have hf : ContDiffAt ℝ 1 (pFlux p : Space n → Space n) (gradient u x) :=
    (contDiffAt_pFlux p (hg x hx)).of_le (by simp)
  exact (hf.comp x (hgrad.contDiffAt (hΩ.mem_nhds hx))).contDiffWithinAt

theorem continuousOn_coordinateDivergence_of_contDiffOn_one {n : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {F : Space n → Space n}
    (hF : ContDiffOn ℝ 1 F Ω) : ContinuousOn (coordinateDivergence F) Ω := by
  unfold coordinateDivergence
  apply continuousOn_finsetSum
  intro i _
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn
    (continuousOn_gradient_of_contDiffOn_one hΩ
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hF))

/-- A continuous function whose genuine compact smooth test integrals vanish
is zero throughout its open domain, by the fundamental lemma and open-positive
Lebesgue measure. No distributional uniqueness hypothesis is supplied. -/
theorem eqOn_zero_of_continuousOn_integral_smoothTests_eq_zero {n : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {f : Space n → ℝ}
    (hf : ContinuousOn f Ω)
    (hint : ∀ φ : Space n → ℝ, SmoothTest Ω φ → ∫ x in Ω, f x * φ x = 0) :
    ∀ x ∈ Ω, f x = 0 := by
  have hae : ∀ᵐ x ∂volume, x ∈ Ω → f x = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrableOn hΩ.measurableSet)
    intro φ hφ hφc hφΩ
    have hsupp : ∀ x, x ∉ Ω → φ x * f x = 0 := by
      intro x hx
      have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx (hφΩ h))
      rw [hz,zero_mul]
    change (∫ x, φ x * f x) = 0
    rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    simpa only [mul_comm] using hint φ ⟨hφ,hφc,hφΩ⟩
  have haer : f =ᵐ[volume.restrict Ω] (fun _ => 0) :=
    (ae_restrict_iff' hΩ.measurableSet).mpr hae
  intro x hx
  exact Measure.eqOn_open_of_ae_eq haer hΩ hf continuousOn_const hx

/-- Genuine local C2 classical solutions with nonzero actual gradient satisfy
the full W0-test weak equation; no local Sobolev or flux smoothness premise. -/
theorem weakPHarmonicPair_of_classicalPLaplacian_eq_zero {n : ℕ} {p : ℝ}
    (hp : 1 < p) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (hg : ∀ x ∈ Ω, gradient u x ≠ 0)
    (hP : ∀ x ∈ Ω, BMCompactAnalytic.classicalPLaplacian p u x = 0) :
    WeakPHarmonicPair p Ω u (gradient u) := by
  have hu1 : ContDiffOn ℝ 1 u Ω := hu.of_le (by norm_num)
  have hf := contDiffOn_pFlux_gradient_of_contDiffOn_two p hΩ hu hg
  apply weakPHarmonicPair_of_divergence_eq_zero_one hp hΩ
    (locallySobolevPair_of_contDiffOn_one hp hΩ hu1)
  · intro i
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hf
  · intro x hx
    have hd := (hf.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
    unfold coordinateDivergence
    rw [←classicalDivergence_eq_sum_gradient_coordinates hd,
      classicalDivergence_pFlux_gradient_eq_classicalPLaplacian p
        (hu.contDiffAt (hΩ.mem_nhds hx)) (hg x hx)]
    exact hP x hx

/-- The weak equation forces the actual classical p-Laplacian to vanish at
all noncritical C2 points. The distributional fundamental lemma is proved in
Mathlib and applied to the actual continuous coordinate divergence. -/
theorem WeakPHarmonicPair.classicalPLaplacian_eq_zero {n : ℕ} {p : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : WeakPHarmonicPair p Ω u (gradient u))
    (hu : ContDiffOn ℝ 2 u Ω) (hg : ∀ x ∈ Ω, gradient u x ≠ 0) :
    ∀ x ∈ Ω, BMCompactAnalytic.classicalPLaplacian p u x = 0 := by
  have hΩ := hw.2.1
  let F : Space n → Space n := fun x => pFlux p (gradient u x)
  have hF : ContDiffOn ℝ 1 F Ω :=
    contDiffOn_pFlux_gradient_of_contDiffOn_two p hΩ hu hg
  have hcoord (i : Fin n) : ContDiffOn ℝ 1 (fun x => F x i) Ω :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hF
  have hz : ∀ x ∈ Ω, coordinateDivergence F x = 0 := by
    apply eqOn_zero_of_continuousOn_integral_smoothTests_eq_zero hΩ
      (continuousOn_coordinateDivergence_of_contDiffOn_one hΩ hF)
    intro φ hφ
    have hi := (integral_inner_gradient_eq_neg_divergence_one hΩ hcoord hφ).2.2
    have hweak := hw.integral_smooth_test_eq_zero hφ
    change (∫ x in Ω, inner ℝ (F x) (gradient φ x)) = 0 at hweak
    rw [hi] at hweak
    linarith
  intro x hx
  rw [←classicalDivergence_pFlux_gradient_eq_classicalPLaplacian p
    (hu.contDiffAt (hΩ.mem_nhds hx)) (hg x hx),
    classicalDivergence_eq_sum_gradient_coordinates
      ((hF.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num))]
  exact hz x hx

theorem weakPHarmonicPair_iff_classicalPLaplacian_eq_zero {n : ℕ} {p : ℝ}
    (hp : 1 < p) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (hg : ∀ x ∈ Ω, gradient u x ≠ 0) :
    WeakPHarmonicPair p Ω u (gradient u) ↔
      ∀ x ∈ Ω, BMCompactAnalytic.classicalPLaplacian p u x = 0 :=
  ⟨fun h => h.classicalPLaplacian_eq_zero hu hg,
    weakPHarmonicPair_of_classicalPLaplacian_eq_zero hp hΩ hu hg⟩

/-- Noncriticality is needed only at the point in question. Continuity of the
actual gradient constructs an open noncritical neighbourhood automatically. -/
theorem WeakPHarmonicPair.classicalPLaplacian_eq_zero_at {n : ℕ} {p : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : WeakPHarmonicPair p Ω u (gradient u))
    (hu : ContDiffOn ℝ 2 u Ω) {x : Space n} (hx : x ∈ Ω)
    (hg : gradient u x ≠ 0) : BMCompactAnalytic.classicalPLaplacian p u x = 0 := by
  let U : Set (Space n) := Ω ∩ {y | gradient u y ≠ 0}
  have hΩ := hw.2.1
  have hc := (contDiffOn_gradient_of_contDiffOn_two hΩ hu).continuousOn
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    exact inter_mem (hΩ.mem_nhds hy.1)
      ((hc.continuousAt (hΩ.mem_nhds hy.1)).preimage_mem_nhds
        (isOpen_ne.mem_nhds hy.2))
  exact (hw.mono inter_subset_left hU).classicalPLaplacian_eq_zero
    (hu.mono inter_subset_left) (fun y hy => hy.2) x ⟨hx,hg⟩

/-- Actual uniqueness of distributional gradients replaces any supplied weak
gradient representative by the genuine classical gradient of a local C1 u. -/
theorem WeakPHarmonicPair.with_classical_gradient {n : ℕ} {p : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hw : WeakPHarmonicPair p Ω u g) (hu : ContDiffOn ℝ 1 u Ω) :
    WeakPHarmonicPair p Ω u (gradient u) := by
  have hs := locallySobolevPair_of_contDiffOn_one hw.1 hw.2.1 hu
  refine ⟨hw.1,hw.2.1,hs,?_⟩
  intro D hD θ h hθ
  have hgrad := (hw.2.2.1 D hD).gradient_ae_unique (hs D hD) hD.1
  obtain ⟨hi,he⟩ := hw.2.2.2 D hD θ h hθ
  have hpair : fluxPairing p g h =ᵐ[volume.restrict D]
      fluxPairing p (gradient u) h := by
    filter_upwards [hgrad] with x hx
    simp only [fluxPairing,hx]
  exact ⟨hi.congr hpair, by rw [←integral_congr_ae hpair]; exact he⟩

theorem IsWeakPHarmonic.classicalPLaplacian_eq_zero_at {n : ℕ} {p : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} (hw : IsWeakPHarmonic p Ω u)
    (hu : ContDiffOn ℝ 2 u Ω) {x : Space n} (hx : x ∈ Ω)
    (hg : gradient u x ≠ 0) : BMCompactAnalytic.classicalPLaplacian p u x = 0 := by
  obtain ⟨g,hw⟩ := hw
  exact (hw.with_classical_gradient (hu.of_le (by norm_num))).classicalPLaplacian_eq_zero_at hu hx hg

end BMCompactPDE
end
end
end
end V5SegmentClassicalPLaplaceBridge


/-! Exact development proof segment: ClassicalViscosityCore -/
section V5SegmentClassicalViscosityCore

/-! Actual C2 upper contact, classical-to-viscosity bridge, and strict
viscosity comparison. The manuscript convention is obtained as a consequence.
No weak regularity or non-strict critical-point comparison is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
/- Checked-source candidate segment: C2TouchingOrder -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem fderiv_eq_of_local_upper_contact {u φ : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hφ : DifferentiableAt ℝ φ x)
    (hv : u x = φ x) (htouch : ∀ᶠ y in 𝓝 x, u y ≤ φ y) :
    fderiv ℝ u x = fderiv ℝ φ x := by
  have hm : IsLocalMin (fun y => φ y - u y) x := by
    filter_upwards [htouch] with y hy
    simpa only [←hv,sub_self] using (sub_nonneg.mpr hy)
  have hz := hm.fderiv_eq_zero
  rw [fderiv_fun_sub hφ hu] at hz
  exact (sub_eq_zero.mp hz).symm

theorem gradient_eq_of_local_upper_contact {u φ : E → ℝ} {x : E}
    (hu : DifferentiableAt ℝ u x) (hφ : DifferentiableAt ℝ φ x)
    (hv : u x = φ x) (htouch : ∀ᶠ y in 𝓝 x, u y ≤ φ y) :
    gradient u x = gradient φ x := by
  unfold gradient
  rw [fderiv_eq_of_local_upper_contact hu hφ hv htouch]

theorem hessian_le_of_local_upper_contact {u φ : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hφ : ContDiffAt ℝ 2 φ x)
    (hv : u x = φ x) (htouch : ∀ᶠ y in 𝓝 x, u y ≤ φ y) (e : E) :
    actualHessian u x e e ≤ actualHessian φ x e e := by
  let C : ℝ → E := quadraticCurve x e 0
  have hC : ContDiffAt ℝ 2 C 0 := quadraticCurve_contDiffAt x e 0
  have hCx : C 0 = x := by simp [C]
  have huC : ContDiffAt ℝ 2 (fun r => u (C r)) 0 := by
    have hu' : ContDiffAt ℝ 2 u (C 0) := by simpa only [hCx] using hu
    exact hu'.comp (0 : ℝ) hC
  have hφC : ContDiffAt ℝ 2 (fun r => φ (C r)) 0 := by
    have hφ' : ContDiffAt ℝ 2 φ (C 0) := by simpa only [hCx] using hφ
    exact hφ'.comp (0 : ℝ) hC
  have hd := fderiv_eq_of_local_upper_contact
    (hu.differentiableAt (by norm_num)) (hφ.differentiableAt (by norm_num)) hv htouch
  have hder : deriv (fun r => u (C r)) 0 = deriv (fun r => φ (C r)) 0 := by
    rw [quadraticCurve_comp_deriv (hu.differentiableAt (by norm_num)),
      quadraticCurve_comp_deriv (hφ.differentiableAt (by norm_num)),hd]
  have hc : ∀ᶠ r in 𝓝 (0 : ℝ), min (u (C r)) (u (C r)) ≤ φ (C r) := by
    have ht : Tendsto C (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa only [hCx] using hC.continuousAt.tendsto
    simpa only [min_self] using ht.eventually htouch
  have hb := min_le_second_derivative_of_local_min_comparison huC huC hφC
    (by simpa only [hCx] using hv) (by simpa only [hCx] using hv) hder hder hc
  simp only [min_self] at hb
  rw [quadraticCurve_comp_second_deriv hu,quadraticCurve_comp_second_deriv hφ] at hb
  simpa only [actualHessian,smul_zero,map_zero,add_zero] using hb

theorem normalizedPLaplacian_le_of_local_upper_contact {p : ℝ} (hp : 1 < p)
    {u φ : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hφ : ContDiffAt ℝ 2 φ x)
    (hv : u x = φ x) (htouch : ∀ᶠ y in 𝓝 x, u y ≤ φ y)
    (hg : gradient φ x ≠ 0) :
    normalizedPLaplacian p u x ≤ normalizedPLaplacian p φ x := by
  have hgu := gradient_eq_of_local_upper_contact
    (hu.differentiableAt (by norm_num)) (hφ.differentiableAt (by norm_num)) hv htouch
  have hgu0 : gradient u x ≠ 0 := by rwa [hgu]
  obtain ⟨ν,a,b,d,hν,ha,hb,hd,hA,hB,hD,_⟩ :=
    unit_normal_of_positive_proportional (t := (0 : ℝ))
      (α := (1 : ℝ)) (β := (1 : ℝ)) (by norm_num) (by norm_num)
      hgu0 (by simpa using hgu.symm) (by simpa using hgu.symm) (by norm_num)
  have hh := aligned_normalizedPLaplacian_comparison (c₁ := (1 : ℝ)) (c₂ := (0 : ℝ))
    hp ha hb hd hν hA hB hD
    (fun e => by simpa using hessian_le_of_local_upper_contact hu hφ hv htouch e)
  simpa using hh


/- Checked-source candidate segment: ViscosityStructure -/

theorem gradient_add_const (f : E → ℝ) (c : ℝ) (x : E) :
    gradient (fun y => f y + c) x = gradient f x := by
  simp only [gradient,fderiv_add_const]

theorem actualHessian_add_const (f : E → ℝ) (c : ℝ) (x : E) :
    actualHessian (fun y => f y + c) x = actualHessian f x := by
  unfold actualHessian
  have hh : fderiv ℝ (fun y => f y + c) = fderiv ℝ f :=
    funext (fun y => fderiv_add_const c)
  rw [hh]

theorem actualLaplacian_add_const (f : E → ℝ) (c : ℝ) (x : E) :
    actualLaplacian (fun y => f y + c) x = actualLaplacian f x := by
  simp only [actualLaplacian,actualHessianEnd,actualHessian_add_const]

theorem normalizedPLaplacian_add_const (p : ℝ) (f : E → ℝ) (c : ℝ) (x : E) :
    normalizedPLaplacian p (fun y => f y + c) x = normalizedPLaplacian p f x := by
  simp only [normalizedPLaplacian,actualLaplacian_add_const,
    gradient_add_const,actualHessian_add_const]

theorem IsViscosityPSubsolution.mono {p : ℝ} {Ω D : Set E} {u : E → ℝ}
    (hu : IsViscosityPSubsolution p Ω u) (hD : IsOpen D) (hDΩ : D ⊆ Ω) :
    IsViscosityPSubsolution p D u :=
  ⟨hu.1,hD,hu.2.2.1.mono hDΩ,fun x hx => hu.2.2.2 x (hDΩ hx)⟩

/-- The stronger local non-strict convention entails exactly the manuscript's
global strict test condition. The converse is not claimed here. -/
theorem IsViscosityPSubsolution.manuscript {p : ℝ} {Ω : Set E} {u : E → ℝ}
    (hu : IsViscosityPSubsolution p Ω u) : IsManuscriptViscosityPSubsolution p Ω u := by
  refine ⟨hu.1,hu.2.1,hu.2.2.1,?_⟩
  intro x hx φ hφ hv hstrict hg
  apply hu.2.2.2 x hx φ (hφ.contDiffAt (hu.2.1.mem_nhds hx)) hv _ hg
  filter_upwards [hu.2.1.mem_nhds hx] with y hy
  by_cases hxy : y = x
  · simpa only [hxy] using hv.le
  · exact (hstrict y hy hxy).le

theorem IsViscosityPSubsolution.add_const {p : ℝ} {Ω : Set E} {u : E → ℝ}
    (hu : IsViscosityPSubsolution p Ω u) (c : ℝ) :
    IsViscosityPSubsolution p Ω (fun y => u y + c) := by
  refine ⟨hu.1,hu.2.1,hu.2.2.1.add upperSemicontinuousOn_const,?_⟩
  intro x hx φ hφ hv htouch hg
  have hv' : u x = φ x + (-c) := by linarith
  have ht' : ∀ᶠ y in 𝓝 x, u y ≤ φ y + (-c) := by
    filter_upwards [htouch] with y hy
    linarith
  have hg' : gradient (fun y => φ y + (-c)) x ≠ 0 := by
    simpa only [gradient_add_const] using hg
  have h := hu.2.2.2 x hx (fun y => φ y + (-c))
    (hφ.add contDiffAt_const) hv' ht' hg'
  simpa only [normalizedPLaplacian_add_const] using h


/- Checked-source candidate segment: ClassicalViscosity -/

theorem viscosityPSubsolution_of_classical_normalized {p : ℝ} (hp : 1 < p)
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (hP : ∀ x ∈ Ω, gradient u x ≠ 0 → 0 ≤ normalizedPLaplacian p u x) :
    IsViscosityPSubsolution p Ω u := by
  refine ⟨hp,hΩ,hu.continuousOn.upperSemicontinuousOn,?_⟩
  intro x hx φ hφ hv htouch hg
  have huAt := hu.contDiffAt (hΩ.mem_nhds hx)
  have hgrad := gradient_eq_of_local_upper_contact
    (huAt.differentiableAt (by norm_num)) (hφ.differentiableAt (by norm_num)) hv htouch
  have hgu : gradient u x ≠ 0 := by rwa [hgrad]
  exact (hP x hx hgu).trans
    (normalizedPLaplacian_le_of_local_upper_contact hp huAt hφ hv htouch hg)

theorem viscosityPSubsolution_of_classical_eq_zero {p : ℝ} (hp : 1 < p)
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (hP : ∀ x ∈ Ω, gradient u x ≠ 0 → classicalPLaplacian p u x = 0) :
    IsViscosityPSubsolution p Ω u := by
  apply viscosityPSubsolution_of_classical_normalized hp hΩ hu
  intro x hx hg
  exact (normalizedPLaplacian_eq_zero_of_classical_eq_zero hg (hP x hx hg)).ge

theorem manuscriptViscosityPSubsolution_of_classical_eq_zero {p : ℝ} (hp : 1 < p)
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ} (hu : ContDiffOn ℝ 2 u Ω)
    (hP : ∀ x ∈ Ω, gradient u x ≠ 0 → classicalPLaplacian p u x = 0) :
    IsManuscriptViscosityPSubsolution p Ω u :=
  (viscosityPSubsolution_of_classical_eq_zero hp hΩ hu hP).manuscript


/- Checked-source candidate segment: StrictViscosityComparison -/

theorem IsViscosityPSubsolution.leOn_of_strict_classical_supersolution
    {p : ℝ} {Ω D : Set E} {u h : E → ℝ}
    (hu : IsViscosityPSubsolution p Ω u)
    (hD : IsOpen D) (hDb : Bornology.IsBounded D) (hDO : closure D ⊆ Ω)
    (hh : ContinuousOn h (closure D)) (hC2 : ContDiffOn ℝ 2 h D)
    (hgrad : ∀ x ∈ D, gradient h x ≠ 0)
    (hstrict : ∀ x ∈ D, normalizedPLaplacian p h x < 0)
    (hboundary : ∀ x ∈ frontier D, u x ≤ h x) :
    ∀ x ∈ D, u x ≤ h x := by
  intro y hy
  by_contra hbad
  have hne : (closure D).Nonempty := ⟨y,subset_closure hy⟩
  have hf : UpperSemicontinuousOn (fun q => u q - h q) (closure D) := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using!
      (hu.2.2.1.mono hDO).add hh.neg.upperSemicontinuousOn
  obtain ⟨x,hx,hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hne hDb.isCompact_closure hf
  have hpos : 0 < u x - h x :=
    (sub_pos.mpr (lt_of_not_ge hbad)).trans_le (hmax (subset_closure hy))
  have hxD : x ∈ D := by
    by_contra hxn
    have hxf : x ∈ frontier D := by
      rw [hD.frontier_eq]
      exact ⟨hx,hxn⟩
    have hb := hboundary x hxf
    linarith
  let φ : E → ℝ := fun q => h q + (u x - h x)
  have hφ : ContDiffAt ℝ 2 φ x :=
    (hC2.contDiffAt (hD.mem_nhds hxD)).add contDiffAt_const
  have hv : u x = φ x := by dsimp [φ]; ring
  have htouch : ∀ᶠ q in 𝓝 x, u q ≤ φ q := by
    filter_upwards [hD.mem_nhds hxD] with q hq
    have hb := hmax (subset_closure hq)
    change u q - h q ≤ u x - h x at hb
    dsimp only [φ]
    linarith
  have hg : gradient φ x ≠ 0 := by
    simpa only [φ,gradient_add_const] using hgrad x hxD
  have hb := hu.2.2.2 x (hDO (subset_closure hxD)) φ hφ hv htouch hg
  have hn : 0 ≤ normalizedPLaplacian p h x := by
    simpa only [φ,normalizedPLaplacian_add_const] using hb
  exact (not_le_of_gt (hstrict x hxD)) hn

end BMCompactAnalytic
end
end V5SegmentClassicalViscosityCore


/-! Exact development proof segment: SobolevGraphClosure -/
section V5SegmentSobolevGraphClosure

/-! The concrete distributional gradient graph is closed under actual Lp
convergence. No weak-gradient equation for the limit is supplied as a premise.
This is the closure tool needed for nonsmooth truncations. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

theorem memLp_coordinate {n : ℕ} {q : ℝ≥0∞} {μ : Measure (Space n)}
    {g : Space n → Space n} (hg : MemLp g q μ) (i : Fin n) :
    MemLp (fun x => g x i) q μ := by
  exact hg.of_le ((EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hg.1)
    (Eventually.of_forall (fun x => PiLp.norm_apply_le (g x) i))

theorem tendsto_eLpNorm_coordinate_sub {n : ℕ} {q : ℝ≥0∞}
    {μ : Measure (Space n)} {g : ℕ → Space n → Space n} {h : Space n → Space n}
    (hlim : Tendsto (fun j => eLpNorm (fun x => g j x-h x) q μ) atTop (𝓝 0))
    (i : Fin n) :
    Tendsto (fun j => eLpNorm (fun x => g j x i-h x i) q μ) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le)
  intro j
  exact eLpNorm_mono_ae (Eventually.of_forall (fun x => by
    simpa only [PiLp.sub_apply] using PiLp.norm_apply_le (g j x-h x) i))

theorem tendsto_integral_mul_of_eLpNorm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {P Q : ℝ≥0∞} [ENNReal.HolderTriple P Q 1]
    {u : ℕ → α → ℝ} {v ψ : α → ℝ}
    (hu : ∀ j, MemLp (u j) P μ) (hv : MemLp v P μ) (hψ : MemLp ψ Q μ)
    (hlim : Tendsto (fun j => eLpNorm (u j-v) P μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, u j x*ψ x ∂μ) atTop (𝓝 (∫ x, v x*ψ x ∂μ)) := by
  have hbound (j : ℕ) : eLpNorm ((fun x => u j x*ψ x)-(fun x => v x*ψ x)) 1 μ ≤
      eLpNorm (u j-v) P μ * eLpNorm ψ Q μ := by
    have hb := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm
      (p := P) (q := Q) (r := 1)
      ((hu j).sub hv).1 hψ.1 (fun a b : ℝ => a*b) (1 : ℝ≥0)
      (Eventually.of_forall (fun x => by simp only [norm_mul,NNReal.coe_one,one_mul]; exact le_rfl))
    simpa only [Pi.sub_def,Pi.sub_apply,sub_mul,ENNReal.coe_one,one_mul] using! hb
  have hL1 : Tendsto (fun j =>
      eLpNorm ((fun x => u j x*ψ x)-(fun x => v x*ψ x)) 1 μ) atTop (𝓝 0) := by
    have hc := ENNReal.Tendsto.mul_const hlim (Or.inr hψ.eLpNorm_ne_top)
    rw [zero_mul] at hc
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
      (fun _ => bot_le) hbound
  exact tendsto_integral_of_L1' (fun x => v x*ψ x) (hv.integrable_mul hψ).1
    (Eventually.of_forall (fun j => (hu j).integrable_mul hψ)) hL1

/-- Closedness of the genuine distributional gradient graph in both Lp
components. The limits' Lp membership is explicit; their weak equation is derived. -/
theorem hasWeakGradientOn_of_eLpNorm_limits {n : ℕ} {p : ℝ} (hp : 1<p)
    {Ω : Set (Space n)} {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hu : ∀ j, SobolevPair p Ω (u j) (g j))
    (hv : MemLp v (ENNReal.ofReal p) (volume.restrict Ω))
    (hh : MemLp h (ENNReal.ofReal p) (volume.restrict Ω))
    (hlimu : Tendsto (fun j => eLpNorm (u j-v) (ENNReal.ofReal p)
      (volume.restrict Ω)) atTop (𝓝 0))
    (hlimg : Tendsto (fun j => eLpNorm (fun x => g j x-h x) (ENNReal.ofReal p)
      (volume.restrict Ω)) atTop (𝓝 0)) : HasWeakGradientOn Ω v h := by
  letI := (holderConjugate_p_dual hp).symm
  intro φ hφ i
  let μ := volume.restrict Ω
  let Q : ℝ≥0∞ := ENNReal.ofReal (p/(p-1))
  have hφQ : MemLp φ Q μ :=
    (BMCompactCapacityV2.smooth_compactSupport_memLp Q hφ.1 hφ.2.1).restrict Ω
  have hdφQ : MemLp (fun x => gradient φ x i) Q μ :=
    memLp_coordinate
      ((BMCompactCapacityV2.gradient_smooth_compactSupport_memLp Q hφ.1 hφ.2.1).restrict Ω) i
  have hhi := memLp_coordinate hh i
  have hleft := tendsto_integral_mul_of_eLpNorm (fun j => (hu j).2.1) hv hdφQ hlimu
  have hright := tendsto_integral_mul_of_eLpNorm
    (fun j => memLp_coordinate (hu j).2.2.1 i) hhi hφQ
    (tendsto_eLpNorm_coordinate_sub hlimg i)
  refine ⟨hv.integrable_mul hdφQ,hhi.integrable_mul hφQ,?_⟩
  have heq : (fun j => ∫ x in Ω, u j x*gradient φ x i) =
      (fun j => -(∫ x in Ω, g j x i*φ x)) :=
    funext (fun j => ((hu j).2.2.2 φ hφ i).2.2)
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright.neg

theorem sobolevPair_of_eLpNorm_limits {n : ℕ} {p : ℝ} (hp : 1<p)
    {Ω : Set (Space n)} {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hu : ∀ j, SobolevPair p Ω (u j) (g j))
    (hv : MemLp v (ENNReal.ofReal p) (volume.restrict Ω))
    (hh : MemLp h (ENNReal.ofReal p) (volume.restrict Ω))
    (hlimu : Tendsto (fun j => eLpNorm (u j-v) (ENNReal.ofReal p)
      (volume.restrict Ω)) atTop (𝓝 0))
    (hlimg : Tendsto (fun j => eLpNorm (fun x => g j x-h x) (ENNReal.ofReal p)
      (volume.restrict Ω)) atTop (𝓝 0)) : SobolevPair p Ω v h :=
  ⟨hp,hv,hh,hasWeakGradientOn_of_eLpNorm_limits hp hu hv hh hlimu hlimg⟩

end BMCompactPDE
end
end V5SegmentSobolevGraphClosure


/-! Exact development proof segment: W0Truncation -/
section V5SegmentW0Truncation

/-! Closed W0 graph, actual flat composition and positive-part truncation
for arbitrary nonsmooth Sobolev representatives. All approximating sequences,
weak gradient identities and chain-rule Lp limits are constructed explicitly. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

theorem eLpNorm_sub_le_via {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {q : ℝ≥0∞} (hq : 1≤q) {f g h : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) :
    eLpNorm (f-h) q μ ≤ eLpNorm (f-g) q μ+eLpNorm (g-h) q μ := by
  have heq : f-h = (f-g)+(g-h) := by
    ext x
    simp only [Pi.sub_apply,Pi.add_apply]
    abel
  rw [heq]
  exact eLpNorm_add_le (hf.sub hg) (hg.sub hh) hq

/-- The concrete zero-boundary Sobolev graph is closed in its two Lp
components. The proof chooses an actual smooth approximant from every row. -/
theorem zeroBoundarySobolevPair_of_eLpNorm_limits {n : ℕ} {p : ℝ} (hp : 1<p)
    {Ω : Set (Space n)} {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hu : ∀ j, ZeroBoundarySobolevPair p Ω (u j) (g j))
    (hv : MemLp v (ENNReal.ofReal p) (volume.restrict Ω))
    (hh : MemLp h (ENNReal.ofReal p) (volume.restrict Ω))
    (hlimu : Tendsto (fun j => eLpNorm (u j-v) (ENNReal.ofReal p)
      (volume.restrict Ω)) atTop (𝓝 0))
    (hlimg : Tendsto (fun j => eLpNorm (fun x => g j x-h x) (ENNReal.ofReal p)
      (volume.restrict Ω)) atTop (𝓝 0)) : ZeroBoundarySobolevPair p Ω v h := by
  let μ := volume.restrict Ω
  let q := ENNReal.ofReal p
  let ε : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (((j : ℝ)+1)⁻¹)
  have hεpos (j : ℕ) : 0<ε j :=
    ENNReal.ofReal_pos.mpr (inv_pos.mpr (by positivity))
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hnat : Tendsto (fun j : ℕ => (j : ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [ε,Function.comp_def,ENNReal.ofReal_zero] using!
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_inv_atTop_zero.comp hnat)
  have hex (j : ℕ) : ∃ φ : Space n → ℝ, SmoothTest Ω φ ∧
      eLpNorm (φ-u j) q μ < ε j ∧
      eLpNorm (fun x => gradient φ x-g j x) q μ < ε j := by
    obtain ⟨_,a,ha,hau,hag⟩ := hu j
    have he1 := hau.eventually (eventually_lt_nhds (hεpos j))
    have he2 := hag.eventually (eventually_lt_nhds (hεpos j))
    obtain ⟨k,hk1,hk2⟩ := (he1.and he2).exists
    exact ⟨a k,ha k,hk1,hk2⟩
  choose φ hφ hφu hφg using hex
  have hq : 1≤q := ENNReal.one_le_ofReal.mpr hp.le
  have hφmem (j : ℕ) : SobolevPair p Ω (φ j) (gradient (φ j)) :=
    (hφ j).sobolevPair hp
  refine ⟨sobolevPair_of_eLpNorm_limits hp (fun j => (hu j).1) hv hh hlimu hlimg,
    φ,hφ,?_,?_⟩
  · have hb (j : ℕ) : eLpNorm (φ j-v) q μ ≤
        ε j+eLpNorm (u j-v) q μ :=
      (eLpNorm_sub_le_via hq (hφmem j).2.1.1 (hu j).1.2.1.1 hv.1).trans
        (add_le_add (hφu j).le le_rfl)
    have hbnd := hεlim.add hlimu
    rw [add_zero] at hbnd
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbnd
      (fun _ => bot_le) hb
  · have hb (j : ℕ) : eLpNorm (fun x => gradient (φ j) x-h x) q μ ≤
        ε j+eLpNorm (fun x => g j x-h x) q μ := by
      have ht : eLpNorm (gradient (φ j)-h) q μ ≤
          eLpNorm (gradient (φ j)-g j) q μ+eLpNorm (g j-h) q μ :=
        eLpNorm_sub_le_via hq (hφmem j).2.2.1.1 (hu j).1.2.2.1.1 hh.1
      simpa only [Pi.sub_def] using! ht.trans (add_le_add (hφg j).le le_rfl)
    have hbnd := hεlim.add hlimg
    rw [add_zero] at hbnd
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbnd
      (fun _ => bot_le) hb


theorem continuous_positivePartSlope (k : ℕ) : Continuous (positivePartSlope k) := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hc : Continuous (fun t : ℝ => ((k : ℝ)+1)*t) := continuous_const.mul continuous_id
  exact (Real.smoothTransition.continuous.comp hc).add
    (hc.mul ((hs.continuous_deriv (by simp)).comp hc))

theorem smoothPositivePart_norm_sub_le (k : ℕ) {C : ℝ}
    (hC : ∀ t, ‖positivePartSlope k t‖≤C) (a b : ℝ) :
    ‖BMCompactPDE.smoothPositivePart k a-BMCompactPDE.smoothPositivePart k b‖ ≤ C*‖a-b‖ := by
  apply convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (smoothPositivePart_hasDerivAt k t).differentiableAt)
    (fun t _ => ?_) (mem_univ b) (mem_univ a)
  rw [(smoothPositivePart_hasDerivAt k t).deriv]
  exact hC t

theorem tendsto_eLpNorm_bounded_smul {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure α} {q : ℝ≥0∞}
    (hq0 : q≠0) (hqt : q≠(∞ : ℝ≥0∞)) (hq : 1≤q)
    {a : ℕ → α → ℝ} {b : α → ℝ} {g : ℕ → α → E} {h : α → E}
    {C : ℝ} (hC : 0≤C)
    (ha : ∀ j, AEStronglyMeasurable (a j) μ) (hb : AEStronglyMeasurable b μ)
    (hg : ∀ j, MemLp (g j) q μ) (hh : MemLp h q μ)
    (haC : ∀ j x, ‖a j x‖≤C) (hbC : ∀ x, ‖b x‖≤C)
    (halim : ∀ᵐ x ∂μ, Tendsto (fun j => a j x) atTop (𝓝 (b x)))
    (hglim : Tendsto (fun j => eLpNorm (g j-h) q μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun x => a j x • g j x-b x • h x) q μ)
      atTop (𝓝 0) := by
  let A : ℕ → α → E := fun j x => a j x • (g j x-h x)
  let B : ℕ → α → E := fun j x => (a j x-b x) • h x
  have hAm (j : ℕ) : AEStronglyMeasurable (A j) μ :=
    (ha j).smul ((hg j).sub hh).1
  have hBm (j : ℕ) : AEStronglyMeasurable (B j) μ :=
    ((ha j).sub hb).smul hh.1
  have hAlim : Tendsto (fun j => eLpNorm (A j) q μ) atTop (𝓝 0) := by
    have hbnd (j : ℕ) : eLpNorm (A j) q μ ≤ ‖C‖ₑ*eLpNorm (g j-h) q μ := by
      rw [←eLpNorm_const_smul]
      apply eLpNorm_mono
      intro x
      simp only [A,norm_smul,Pi.smul_apply,Pi.sub_apply,Real.norm_eq_abs,
        abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (haC j x) (norm_nonneg _)
    have ht := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ) hglim (Or.inr enorm_ne_top)
    rw [mul_zero] at ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le) hbnd
  have hBlim : Tendsto (fun j => eLpNorm (B j) q μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_zero_of_dominated hq0 hqt (b := (2*C) • h) hBm
      (hh.const_smul (2*C))
    · intro j
      exact Eventually.of_forall (fun x => by
        calc ‖B j x‖ = ‖a j x-b x‖*‖h x‖ := norm_smul _ _
             _ ≤ (‖a j x‖+‖b x‖)*‖h x‖ :=
               mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)
             _ ≤ (C+C)*‖h x‖ :=
               mul_le_mul_of_nonneg_right (add_le_add (haC j x) (hbC x)) (norm_nonneg _)
             _ = ‖((2*C) • h) x‖ := by
               simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤2*C)]
               ring)
    · filter_upwards [halim] with x hx
      have hc : Tendsto (fun j => a j x-b x) atTop (𝓝 0) := by
        simpa only [sub_self] using hx.sub_const (b x)
      simpa only [B,zero_smul] using hc.smul_const (h x)
  have hbnd (j : ℕ) : eLpNorm (fun x => a j x • g j x-b x • h x) q μ ≤
      eLpNorm (A j) q μ+eLpNorm (B j) q μ := by
    have heq : (fun x => a j x • g j x-b x • h x) = A j+B j := by
      funext x
      dsimp only [A,B,Pi.add_apply]
      rw [smul_sub,sub_smul]
      abel
    rw [heq]
    exact eLpNorm_add_le (hAm j) (hBm j) hq
  have ht := hAlim.add hBlim
  rw [add_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hbnd

/-- Fixed flat smooth truncation preserves arbitrary W0 pairs, with its actual
chain-rule gradient. A subsequence and actual Lp limits prove the statement. -/
theorem ZeroBoundarySobolevPair.smoothPositivePart {n : ℕ} {p : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p Ω u g) (k : ℕ) :
    ZeroBoundarySobolevPair p Ω (fun x => BMCompactPDE.smoothPositivePart k (u x))
      (fun x => positivePartSlope k (u x) • g x) := by
  obtain ⟨hSob,φ,hφ,hLu,hLg⟩ := hu
  let μ := volume.restrict Ω
  let q := ENNReal.ofReal p
  have hp : 1<p := hSob.1
  have hq0 : q≠0 := ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp)
  have hqt : q≠(∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hq : 1≤q := ENNReal.one_le_ofReal.mpr hp.le
  have hφSob (j : ℕ) := (hφ j).sobolevPair hp
  have hmeas (j : ℕ) : AEStronglyMeasurable (φ j) μ := (hφSob j).2.1.1
  have hmeasure := tendstoInMeasure_of_tendsto_eLpNorm hq0 hmeas hSob.2.1.1 hLu
  obtain ⟨σ,hσ,hσlim⟩ := hmeasure.exists_seq_tendsto_ae
  obtain ⟨C,hC,hbound⟩ := positivePartSlope_uniform_bound
  have hC0 : 0≤C := zero_le_one.trans hC
  let ψ : ℕ → Space n → ℝ := fun j x => BMCompactPDE.smoothPositivePart k (φ (σ j) x)
  have hψ (j : ℕ) : SmoothTest Ω (ψ j) := by
    have hz : BMCompactPDE.smoothPositivePart k 0 = 0 := smoothPositivePart_eq_zero_of_nonpos k le_rfl
    refine ⟨(smoothPositivePart_contDiff k).comp (hφ (σ j)).1,
      (hφ (σ j)).2.1.comp_left hz,?_⟩
    exact (tsupport_comp_subset hz (φ (σ j))).trans (hφ (σ j)).2.2
  have hVk : MemLp (fun x => BMCompactPDE.smoothPositivePart k (u x)) q μ :=
    hSob.2.1.of_le ((smoothPositivePart_contDiff k).continuous.comp_aestronglyMeasurable hSob.2.1.1)
      (Eventually.of_forall (fun x => smoothPositivePart_norm_le k (u x)))
  have hGkm : AEStronglyMeasurable (fun x => positivePartSlope k (u x) • g x) μ :=
    ((continuous_positivePartSlope k).comp_aestronglyMeasurable hSob.2.1.1).smul hSob.2.2.1.1
  have hGk : MemLp (fun x => positivePartSlope k (u x) • g x) q μ :=
    (hSob.2.2.1.const_smul C).of_le hGkm (Eventually.of_forall (fun x => by
      simp only [norm_smul,Pi.smul_apply,Real.norm_eq_abs,abs_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right (hbound k (u x)) (norm_nonneg _)))
  apply zeroBoundarySobolevPair_of_eLpNorm_limits hp
    (fun j => (hψ j).zeroBoundarySobolevPair hp) hVk hGk
  · have hbnd (j : ℕ) : eLpNorm (ψ j-(fun x => BMCompactPDE.smoothPositivePart k (u x))) q μ ≤
        ‖C‖ₑ*eLpNorm (φ (σ j)-u) q μ := by
      rw [←eLpNorm_const_smul]
      apply eLpNorm_mono
      intro x
      simpa only [ψ,Pi.sub_apply,Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hC0] using
        smoothPositivePart_norm_sub_le k (hbound k) (φ (σ j) x) (u x)
    have ht := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ)
      (hLu.comp hσ.tendsto_atTop) (Or.inr enorm_ne_top)
    rw [mul_zero] at ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun _ => bot_le) hbnd
  · have hgrad (j : ℕ) : gradient (ψ j) =
        fun x => positivePartSlope k (φ (σ j) x) • gradient (φ (σ j)) x := by
      funext x
      exact gradient_smoothPositivePart_comp ((hφ (σ j)).1.differentiable (by simp)) k x
    simp_rw [hgrad]
    apply tendsto_eLpNorm_bounded_smul hq0 hqt hq hC0
      (fun j => (continuous_positivePartSlope k).comp_aestronglyMeasurable (hmeas (σ j)))
      ((continuous_positivePartSlope k).comp_aestronglyMeasurable hSob.2.1.1)
      (fun j => (hφSob (σ j)).2.2.1) hSob.2.2.1
      (fun j x => hbound k (φ (σ j) x)) (fun x => hbound k (u x))
    · filter_upwards [hσlim] with x hx
      exact (continuous_positivePartSlope k).continuousAt.tendsto.comp hx
    · exact hLg.comp hσ.tendsto_atTop

/-- Actual positive-part truncation for nonsmooth zero-boundary Sobolev pairs.
No smoothness of u or prior chain-rule/W0 assertion for its positive part is assumed. -/
theorem ZeroBoundarySobolevPair.positivePart {n : ℕ} {p : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : ZeroBoundarySobolevPair p Ω u g) :
    ZeroBoundarySobolevPair p Ω (fun x => max (u x) 0)
      (fun x => if 0<u x then g x else 0) := by
  let μ := volume.restrict Ω
  let q := ENNReal.ofReal p
  let G : Space n → Space n := fun x => if 0<u x then g x else 0
  have hGn (x : Space n) : ‖G x‖≤‖g x‖ := by
    dsimp only [G]
    split_ifs <;> simp
  have hp : 1<p := hu.1.1
  have hq0 : q≠0 := ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp)
  have hqt : q≠(∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have humeas := hu.1.2.1.1
  have hgmeas := hu.1.2.2.1.1
  have hm : AEStronglyMeasurable (fun x => max (u x) 0) μ :=
    (continuous_id.max continuous_const).comp_aestronglyMeasurable humeas
  have hGm : AEStronglyMeasurable G μ := by
    change AEStronglyMeasurable ({x | 0<u x}.indicator g) μ
    exact hgmeas.indicator₀ (nullMeasurableSet_lt aemeasurable_const humeas.aemeasurable)
  have hmLp : MemLp (fun x => max (u x) 0) q μ :=
    hu.1.2.1.of_le hm (Eventually.of_forall (fun x => by
      by_cases hx : u x≤0
      · simp [max_eq_right hx]
      · rw [max_eq_left (lt_of_not_ge hx).le]))
  have hGLp : MemLp G q μ :=
    hu.1.2.2.1.of_le hGm (Eventually.of_forall hGn)
  apply zeroBoundarySobolevPair_of_eLpNorm_limits hp
    (fun j => hu.smoothPositivePart j) hmLp hGLp
  · apply tendsto_eLpNorm_zero_of_dominated hq0 hqt (b := (2 : ℝ) • u)
    · intro j
      exact ((hu.smoothPositivePart j).1.2.1.1).sub hm
    · exact hu.1.2.1.const_smul (2 : ℝ)
    · intro j
      exact Eventually.of_forall (fun x => by
        have hn : ‖max (u x) 0‖≤‖u x‖ := by
          by_cases hx : u x≤0
          · simp [max_eq_right hx]
          · rw [max_eq_left (lt_of_not_ge hx).le]
        calc ‖BMCompactPDE.smoothPositivePart j (u x)-max (u x) 0‖ ≤
            ‖BMCompactPDE.smoothPositivePart j (u x)‖+‖max (u x) 0‖ := norm_sub_le _ _
             _ ≤ ‖u x‖+‖u x‖ := add_le_add (smoothPositivePart_norm_le j _) hn
             _ = ‖((2 : ℝ) • u) x‖ := by simp [norm_smul]; ring)
    · exact Eventually.of_forall (fun x =>
        tendsto_const_nhds.congr' ((smoothPositivePart_eventually_eq (u x)).mono
          (fun j hj => by simp only [Pi.sub_apply,hj,sub_self])))
  · obtain ⟨C,hC,hbound⟩ := positivePartSlope_uniform_bound
    have hC0 : 0≤C := zero_le_one.trans hC
    apply tendsto_eLpNorm_zero_of_dominated hq0 hqt (b := (C+1) • g)
    · intro j
      exact ((hu.smoothPositivePart j).1.2.2.1.1).sub hGm
    · exact hu.1.2.2.1.const_smul (C+1)
    · intro j
      exact Eventually.of_forall (fun x => by
        calc ‖positivePartSlope j (u x) • g x-G x‖ ≤
            ‖positivePartSlope j (u x) • g x‖+‖G x‖ := norm_sub_le _ _
             _ ≤ C*‖g x‖+‖g x‖ := by
               rw [norm_smul]
               exact add_le_add (mul_le_mul_of_nonneg_right (hbound j _) (norm_nonneg _))
                 (hGn x)
             _ = ‖((C+1) • g) x‖ := by
               simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤C+1)]
               ring)
    · exact Eventually.of_forall (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [positivePartSlope_eventually_eq (u x)] with j hj
        rw [hj]
        simp only [G]
        split_ifs <;> simp)


end BMCompactPDE
end
end V5SegmentW0Truncation


/-! Exact development proof segment: C1Mollification -/
section V5SegmentC1Mollification

/-! Actual normalized bump convolutions, with support control and a genuine
C1 derivative formula. These are density foundations, not a postulated Sobolev
approximation or chain rule. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory ContinuousLinearMap Metric
open scoped Convolution Topology ContDiff Pointwise
namespace BMCompactPDE
abbrev MollifierSpace (n : ℕ) := BMCompactCapacityV2.Space n
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def normalizedMollify (b : ContDiffBump (0 : MollifierSpace n))
    (f : MollifierSpace n → F) : MollifierSpace n → F :=
  b.normed volume ⋆[lsmul ℝ ℝ,volume] f

theorem contDiff_normalizedMollify (b : ContDiffBump (0 : MollifierSpace n))
    {f : MollifierSpace n → F} (hf : Continuous f) :
    ContDiff ℝ ∞ (normalizedMollify b f) := by
  exact b.hasCompactSupport_normed.contDiff_convolution_left _ b.contDiff_normed hf.locallyIntegrable

theorem hasCompactSupport_normalizedMollify (b : ContDiffBump (0 : MollifierSpace n))
    {f : MollifierSpace n → F} (hf : HasCompactSupport f) :
    HasCompactSupport (normalizedMollify b f) :=
  b.hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hf

theorem tsupport_normalizedMollify_subset (b : ContDiffBump (0 : MollifierSpace n))
    {f : MollifierSpace n → F} (hf : HasCompactSupport f) :
    tsupport (normalizedMollify b f) ⊆ closedBall 0 b.rOut + tsupport f := by
  have hclosed : IsClosed (tsupport (b.normed (volume : Measure (MollifierSpace n))) + tsupport f) :=
    (b.hasCompactSupport_normed.isCompact.add hf.isCompact).isClosed
  have hs : tsupport (normalizedMollify b f) ⊆
      tsupport (b.normed (volume : Measure (MollifierSpace n))) + tsupport f :=
    closure_minimal ((support_convolution_subset (lsmul ℝ ℝ)).trans
      (add_subset_add subset_closure subset_closure)) hclosed
  simpa only [b.tsupport_normed_eq] using hs

theorem norm_normalizedMollify_le (b : ContDiffBump (0 : MollifierSpace n))
    {f : MollifierSpace n → F} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (x : MollifierSpace n) :
    ‖normalizedMollify b f x‖ ≤ 3*M := by
  have hd : dist (normalizedMollify b f x) (f x) ≤ 2*M := by
    apply b.dist_normed_convolution_le hf.aestronglyMeasurable
    intro y _
    calc
      dist (f y) (f x) ≤ ‖f y‖ + ‖f x‖ := by simpa only [dist_eq_norm] using norm_sub_le (f y) (f x)
      _ ≤ M+M := add_le_add (hM y) (hM x)
      _ = 2*M := by ring
  have hh := norm_sub_norm_le (normalizedMollify b f x) (f x)
  rw [← dist_eq_norm] at hh
  linarith [hM x]

theorem tendsto_normalizedMollify {b : ℕ → ContDiffBump (0 : MollifierSpace n)}
    (hb : Tendsto (fun j => (b j).rOut) atTop (𝓝 0))
    {f : MollifierSpace n → F} (hf : Continuous f) (x : MollifierSpace n) :
    Tendsto (fun j => normalizedMollify (b j) f x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous hb hf x

theorem fderiv_normalizedMollify (b : ContDiffBump (0 : MollifierSpace n))
    {f : MollifierSpace n → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (x : MollifierSpace n) :
    fderiv ℝ (normalizedMollify b f) x = normalizedMollify b (fderiv ℝ f) x := by
  have hb : ContDiff ℝ ∞ (b.normed (volume : Measure (MollifierSpace n))) := b.contDiff_normed
  have hL : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompR (MollifierSpace n) =
      (lsmul ℝ ℝ : ℝ →L[ℝ] (MollifierSpace n →L[ℝ] ℝ) →L[ℝ] (MollifierSpace n →L[ℝ] ℝ)) := by
    ext a D e
    rfl
  have hd := hc.hasFDerivAt_convolution_right (μ := volume)
    (f := b.normed (volume : Measure (MollifierSpace n))) (lsmul ℝ ℝ)
    hb.continuous.locallyIntegrable hf x
  simpa only [normalizedMollify,hL] using hd.fderiv

theorem tendsto_fderiv_normalizedMollify {b : ℕ → ContDiffBump (0 : MollifierSpace n)}
    (hb : Tendsto (fun j => (b j).rOut) atTop (𝓝 0))
    {f : MollifierSpace n → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (x : MollifierSpace n) :
    Tendsto (fun j => fderiv ℝ (normalizedMollify (b j) f) x) atTop (𝓝 (fderiv ℝ f x)) := by
  simp_rw [fderiv_normalizedMollify _ hf hc]
  exact tendsto_normalizedMollify hb (hf.continuous_fderiv (by norm_num)) x

end BMCompactPDE
end
end V5SegmentC1Mollification


/-! Exact development proof segment: C1CompactDensity -/
section V5SegmentC1CompactDensity

/-! A genuine C1 compact-support function belongs to the concrete W0 graph.
Normalized bump convolutions give actual C∞ compact-support approximants;
their real derivatives converge in Lp by compact support and dominated limits.
No Sobolev density statement or weak-gradient equation is a premise. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff ENNReal Pointwise
namespace BMCompactPDE

theorem tendsto_eLpNorm_zero_of_compact_uniform_bound {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] {μ : Measure (Space n)} [IsLocallyFiniteMeasure μ]
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ (∞ : ℝ≥0∞))
    {K : Set (Space n)} (hK : IsCompact K) {M : ℝ} (hM : 0 ≤ M)
    {f : ℕ → Space n → F} (hmeas : ∀ j, AEStronglyMeasurable (f j) μ)
    (hbound : ∀ j x, ‖f j x‖ ≤ M) (hzero : ∀ j x, x ∉ K → f j x = 0)
    (hlim : ∀ x, Tendsto (fun j => f j x) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (f j) q μ) atTop (𝓝 0) := by
  have hb : MemLp (K.indicator (fun _ : Space n => M)) q μ :=
    memLp_indicator_const q hK.measurableSet M (Or.inr hK.measure_lt_top.ne)
  have ht := tendsto_eLpNorm_zero_of_dominated hq0 hqt
    (f := fun j x => ‖f j x‖) (b := K.indicator (fun _ => M))
    (fun j => (hmeas j).norm) hb
    (fun j => Eventually.of_forall (fun x => by
      by_cases hx : x ∈ K
      · simpa only [indicator_of_mem hx,norm_norm,Real.norm_eq_abs,abs_norm,abs_of_nonneg hM] using hbound j x
      · simp only [hzero j x hx,norm_zero,indicator_of_notMem hx,le_refl]))
    (Eventually.of_forall (fun x => by simpa only [norm_zero] using (hlim x).norm))
  simpa only [eLpNorm_norm] using ht

theorem tendsto_eLpNorm_mollify_sub {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure (Space n)} [IsLocallyFiniteMeasure μ]
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqt : q ≠ (∞ : ℝ≥0∞))
    {b : ℕ → ContDiffBump (0 : Space n)}
    (hblim : Tendsto (fun j => (b j).rOut) atTop (𝓝 0))
    {R : ℝ} (hR : 0 ≤ R) (hbR : ∀ j, (b j).rOut ≤ R)
    {f : Space n → F} (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun j => eLpNorm (normalizedMollify (b j) f - f) q μ) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hf
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hMf (x : Space n) : ‖f x‖ ≤ M := (hC x).trans (le_max_left _ _)
  let K : Set (Space n) := closedBall 0 R + tsupport f
  have hK : IsCompact K := (isCompact_closedBall 0 R).add hc.isCompact
  have hfs : tsupport f ⊆ K := by
    intro x hx
    exact ⟨0,mem_closedBall_self hR,x,hx,zero_add x⟩
  have hjs (j : ℕ) : tsupport (normalizedMollify (b j) f) ⊆ K :=
    (tsupport_normalizedMollify_subset (b j) hc).trans
      (add_subset_add (closedBall_subset_closedBall (hbR j)) Subset.rfl)
  apply tendsto_eLpNorm_zero_of_compact_uniform_bound hq0 hqt hK (M := 4*M) (by positivity)
  · intro j
    exact (contDiff_normalizedMollify (b j) hf).continuous.aestronglyMeasurable.sub hf.aestronglyMeasurable
  · intro j x
    calc
      ‖(normalizedMollify (b j) f - f) x‖ ≤ ‖normalizedMollify (b j) f x‖ + ‖f x‖ := norm_sub_le _ _
      _ ≤ 3*M+M := add_le_add (norm_normalizedMollify_le (b j) hf hMf x) (hMf x)
      _ = 4*M := by ring
  · intro j x hx
    have hf0 : f x = 0 := by
      by_contra hn
      exact hx (hfs (subset_tsupport f hn))
    have hj0 : normalizedMollify (b j) f x = 0 := by
      by_contra hn
      exact hx (hjs j (subset_tsupport _ hn))
    simp only [Pi.sub_apply,hf0,hj0,sub_self]
  · intro x
    simpa only [Pi.sub_apply,sub_self] using! (tendsto_normalizedMollify hblim hf x).sub_const (f x)

theorem zeroBoundarySobolevPair_of_contDiff_one_compactSupport {n : ℕ} {p : ℝ}
    (hp : 1 < p) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {f : Space n → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ω) : ZeroBoundarySobolevPair p Ω f (gradient f) := by
  obtain ⟨δ,hδ,hδO⟩ := hc.isCompact.exists_cthickening_subset_open hΩ hs
  let R : ℕ → ℝ := fun j => δ / ((j : ℝ)+1)
  have hRpos (j : ℕ) : 0 < R j := div_pos hδ (by positivity)
  have hRle (j : ℕ) : R j ≤ δ := by
    dsimp [R]
    apply (div_le_iff₀ (by positivity : 0 < (j : ℝ)+1)).mpr
    have hj : 0 ≤ (j : ℝ) := by positivity
    nlinarith
  let b : ℕ → ContDiffBump (0 : Space n) := fun j =>
    ⟨R j/2,R j,half_pos (hRpos j),half_lt_self (hRpos j)⟩
  have hblim : Tendsto (fun j => (b j).rOut) atTop (𝓝 0) := by
    have hn : Tendsto (fun j : ℕ => (j : ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa only [b,R,div_eq_mul_inv,mul_zero,Function.comp_apply] using!
      (tendsto_const_nhds (x := δ)).mul (tendsto_inv_atTop_zero.comp hn)
  let φ : ℕ → Space n → ℝ := fun j => normalizedMollify (b j) f
  have hφ (j : ℕ) : SmoothTest Ω (φ j) := by
    refine ⟨contDiff_normalizedMollify (b j) hf.continuous,
      hasCompactSupport_normalizedMollify (b j) hc,?_⟩
    apply (tsupport_normalizedMollify_subset (b j) hc).trans
    rintro x ⟨a,ha,y,hy,rfl⟩
    apply hδO
    apply mem_cthickening_of_dist_le (a+y) y δ (tsupport f) hy
    simpa only [dist_eq_norm,add_sub_cancel_right] using
      (mem_closedBall_zero_iff.mp ha).trans (hRle j)
  have hq0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp)
  have hqt : ENNReal.ofReal p ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hu : MemLp f (ENNReal.ofReal p) (volume.restrict Ω) :=
    (hf.continuous.memLp_of_hasCompactSupport hc).restrict Ω
  have hgcont : Continuous (gradient f) :=
    (toDual ℝ (Space n)).symm.continuous.comp (hf.continuous_fderiv (by norm_num))
  have hg : MemLp (gradient f) (ENNReal.ofReal p) (volume.restrict Ω) :=
    (hgcont.memLp_of_hasCompactSupport (BMCompactCapacityV2.gradient_hasCompactSupport hc)).restrict Ω
  have hlimu := tendsto_eLpNorm_mollify_sub (μ := volume.restrict Ω) hq0 hqt
    hblim hδ.le hRle hf.continuous hc
  have hlimd := tendsto_eLpNorm_mollify_sub (μ := volume.restrict Ω) hq0 hqt
    hblim hδ.le hRle (hf.continuous_fderiv (by norm_num)) (hc.fderiv ℝ)
  have hlimgrad : Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-gradient f x)
      (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) := by
    have heq (j : ℕ) : eLpNorm (fun x => gradient (φ j) x-gradient f x)
        (ENNReal.ofReal p) (volume.restrict Ω) =
        eLpNorm (normalizedMollify (b j) (fderiv ℝ f)-fderiv ℝ f)
          (ENNReal.ofReal p) (volume.restrict Ω) := by
      apply eLpNorm_congr_norm_ae
      exact Eventually.of_forall (fun x => by
        change ‖(toDual ℝ (Space n)).symm (fderiv ℝ (φ j) x) -
          (toDual ℝ (Space n)).symm (fderiv ℝ f x)‖ = _
        rw [←map_sub,LinearIsometryEquiv.norm_map,fderiv_normalizedMollify _ hf hc]
        rfl)
    simpa only [heq] using hlimd
  exact ⟨sobolevPair_of_eLpNorm_limits hp (fun j => (hφ j).sobolevPair hp)
    hu hg hlimu hlimgrad,φ,hφ,hlimu,hlimgrad⟩

end BMCompactPDE
end
end V5SegmentC1CompactDensity


/-! Exact development proof segment: C1BoundaryComparison -/
section V5SegmentC1BoundaryComparison

/-! Actual bounded boundary comparison for globally C1 weak solutions.
An actual compact-support C1 cutoff and proved W0 density/truncation construct
the positive-part test from ordinary pointwise frontier order. General weak
solutions have not been proved C1 here. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace BMCompactPDE

theorem positivePart_sub_zeroBoundary_of_C1_boundary_nonpos
    {n : ℕ} {p : ℝ} (hp : 1 < p) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {d : Space n → ℝ} (hd : ContDiff ℝ 1 d)
    (hboundary : ∀ x ∈ frontier Ω, d x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ZeroBoundarySobolevPair p Ω (fun x => max (d x - ε) 0)
      (fun x => if ε < d x then gradient d x else 0) := by
  let K : Set (Space n) := closure Ω ∩ {x | ε ≤ d x}
  have hK : IsCompact K := hΩb.isCompact_closure.inter_right
    (isClosed_le continuous_const hd.continuous)
  have hKΩ : K ⊆ Ω := by
    intro x hx
    by_contra hxn
    have hxf : x ∈ frontier Ω := by
      rw [hΩ.frontier_eq]
      exact ⟨hx.1, hxn⟩
    have hb := hboundary x hxf
    have he : ε ≤ d x := hx.2
    linarith
  obtain ⟨f, hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hΩ hKΩ
  let χ : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hχcd : ContDiff ℝ ∞ χ :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).comp hf.1
  have hχc : HasCompactSupport χ := hf.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)))
  have hχs : tsupport χ ⊆ Ω :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1
  have hχ0 (x : Space n) : 0 ≤ χ x := Real.smoothTransition.nonneg _
  have hχ1 (x : Space n) (hx : x ∈ K) : χ x = 1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)
  let ψ : Space n → ℝ := fun x => χ x * (d x - ε)
  have hψcd : ContDiff ℝ 1 ψ :=
    (hχcd.of_le (by simp)).mul (hd.sub contDiff_const)
  have hψc : HasCompactSupport ψ := hχc.mul_right
  have hψs : tsupport ψ ⊆ Ω := tsupport_mul_subset_left.trans hχs
  have hW := (zeroBoundarySobolevPair_of_contDiff_one_compactSupport
    hp hΩ hψcd hψc hψs).positivePart
  have hθeq : EqOn (fun x => max (ψ x) 0) (fun x => max (d x - ε) 0) Ω := by
    intro x hx
    change max (ψ x) 0 = max (d x - ε) 0
    by_cases hex : ε < d x
    · have hχx := hχ1 x ⟨subset_closure hx, hex.le⟩
      dsimp only [ψ]
      rw [hχx, one_mul]
    · have hd0 : d x - ε ≤ 0 := sub_nonpos.mpr (le_of_not_gt hex)
      have hψ0 : ψ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hχ0 x) hd0
      rw [max_eq_right hψ0, max_eq_right hd0]
  have hGeq : EqOn (positivePartGradient ψ (gradient ψ))
      (fun x => if ε < d x then gradient d x else 0) Ω := by
    intro x hx
    by_cases hex : ε < d x
    · have hχx := hχ1 x ⟨subset_closure hx, hex.le⟩
      have hψpos : 0 < ψ x := by
        dsimp only [ψ]
        rw [hχx, one_mul]
        exact sub_pos.mpr hex
      have hN : Ω ∩ {y : Space n | ε < d y} ∈ 𝓝 x :=
        inter_mem (hΩ.mem_nhds hx) ((isOpen_lt continuous_const hd.continuous).mem_nhds hex)
      have heq : ψ =ᶠ[𝓝 x] (fun y => d y - ε) := by
        filter_upwards [hN] with y hy
        have hylt : ε < d y := hy.2
        have hyK : y ∈ K := ⟨subset_closure hy.1, hylt.le⟩
        dsimp only [ψ]
        rw [hχ1 y hyK, one_mul]
      have hgrad : gradient ψ x = gradient d x := by
        unfold gradient
        rw [heq.fderiv_eq, fderiv_sub_const]
      change (if 0 < ψ x then gradient ψ x else 0) =
        (if ε < d x then gradient d x else 0)
      rw [if_pos hψpos, if_pos hex, hgrad]
    · have hd0 : d x - ε ≤ 0 := sub_nonpos.mpr (le_of_not_gt hex)
      have hψ0 : ψ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hχ0 x) hd0
      change (if 0 < ψ x then gradient ψ x else 0) =
        (if ε < d x then gradient d x else 0)
      rw [if_neg (not_lt.mpr hψ0), if_neg hex]
  apply hW.congr
  · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact hθeq hx
  · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact hGeq hx

theorem WeakPHarmonicPair.leOn_of_C1_boundary_order
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u v : Space n → ℝ}
    (hu : WeakPHarmonicPair p Ω u (gradient u))
    (hv : WeakPHarmonicPair p Ω v (gradient v))
    (huc : ContDiff ℝ 1 u) (hvc : ContDiff ℝ 1 v)
    (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ v x) :
    ∀ x ∈ Ω, u x ≤ v x := by
  have hD : LocalDomain Ω (Set.univ : Set (Space n)) :=
    ⟨hu.2.1, hΩb, subset_univ _⟩
  have hSu := sobolevPair_of_contDiffOn_one hu.1 isOpen_univ huc.contDiffOn hD
  have hSv := sobolevPair_of_contDiffOn_one hv.1 isOpen_univ hvc.contDiffOn hD
  have hgrad : gradient (fun x => u x - v x) = fun x => gradient u x - gradient v x :=
    funext (gradient_fun_sub (huc.differentiable (by simp)) (hvc.differentiable (by simp)))
  have heps (ε : ℝ) (hε : 0 < ε) : ∀ x ∈ Ω, u x ≤ v x + ε := by
    have hw := positivePart_sub_zeroBoundary_of_C1_boundary_nonpos hu.1 hu.2.1 hΩb
      (huc.sub hvc) (fun x hx => sub_nonpos.mpr (hboundary x hx)) hε
    have hθ : (fun x => max ((fun y => u y - v y) x - ε) 0) =
        (fun x => max (u x - (v x + ε)) 0) := by
      funext x
      congr 1
      ring
    have hG : (fun x => if ε < (fun y => u y - v y) x then gradient (fun y => u y - v y) x else 0) =
        (fun x => if v x + ε < u x then gradient u x - gradient v x else 0) := by
      funext x
      rw [hgrad]
      have hh : ε < u x - v x ↔ v x + ε < u x := by constructor <;> intro h <;> linarith
      simp only [hh]
    rw [hθ, hG] at hw
    have hSvε : SobolevPair p Ω (fun x => v x + ε) (gradient v) := by
      have hs := hSv.add (sobolevPair_const hu.1 hΩb ε)
      exact hs.congr (Eventually.of_forall (fun x => by simp))
        (Eventually.of_forall (fun x => by simp))
    exact hu.leOn_of_zeroBoundary_positivePart (hv.add_const ε) hSu hSvε hn hΩb hw
      huc.continuous.continuousOn (hvc.continuous.add continuous_const).continuousOn
  intro x hx
  by_contra hnot
  have hpos : 0 < (u x - v x) / 2 := by linarith
  have hb := heps ((u x - v x) / 2) hpos x hx
  linarith

end BMCompactPDE
end
end V5SegmentC1BoundaryComparison


/-! Exact development proof segment: RadialBarrierFoundation -/
section V5SegmentRadialBarrierFoundation

/-! Actual radial p-harmonic primitives for every p>1, including the
subcritical range needed by Theorem A(a). No maximum principle or Hopf lemma
is assumed. The value at the pole has no role in the off-pole assertions. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hasGradientAt_radialPowerPotential_all_p (n : ℕ) (σ : ℝ) {p : ℝ}
    (hp : 1 < p) (hpn : p ≠ (n : ℝ)) {x : E} (hx : x ≠ 0) :
    HasGradientAt (radialPowerPotential n σ p : E → ℝ)
      (normalizedRadialGradient n σ p x) x := by
  let q := (p - (n : ℝ)) / (p - 1)
  let c := σ ^ (-(p - 1)⁻¹)
  have hq : q ≠ 0 := div_ne_zero (sub_ne_zero.mpr hpn)
    (sub_ne_zero.mpr (ne_of_gt hp))
  have hscale : (q⁻¹ * c) * q = c := by field_simp [hq]
  have h := hasGradientAt_scalar_norm_rpow (q⁻¹ * c) q hx
  rw [hscale] at h
  exact h

theorem hasGradientAt_fundamentalPotential_all_p (n : ℕ) (σ : ℝ) {p : ℝ}
    (hp : 1 < p) {x : E} (hx : x ≠ 0) :
    HasGradientAt (fundamentalPotential n σ p : E → ℝ)
      (normalizedRadialGradient n σ p x) x := by
  by_cases hpn : p = (n : ℝ)
  · subst p
    have hf : (fundamentalPotential n σ (n : ℝ) : E → ℝ) =
        criticalRadialPotential n σ := by
      funext y
      simp only [fundamentalPotential,ite_true]
    rw [hf]
    exact hasGradientAt_criticalRadialPotential n σ hx
  · have hf : (fundamentalPotential n σ p : E → ℝ) = radialPowerPotential n σ p := by
      funext y
      simp only [fundamentalPotential,if_neg hpn]
    rw [hf]
    exact hasGradientAt_radialPowerPotential_all_p n σ hp hpn hx

theorem pFlux_gradient_fundamentalPotential_all_p (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hp : 1 < p) {x : E} (hx : x ≠ 0) :
    pFlux p (gradient (fundamentalPotential n σ p : E → ℝ) x) =
      radialSourceFlux n σ x := by
  rw [(hasGradientAt_fundamentalPotential_all_p n σ hp hx).gradient]
  exact pFlux_normalizedRadialGradient n hσ hp hx

theorem contDiffOn_pFlux_gradient_fundamentalPotential_all_p
    (n : ℕ) {σ p : ℝ} (hσ : 0 < σ) (hp : 1 < p) :
    ContDiffOn ℝ ∞
      (fun x : E => pFlux p (gradient (fundamentalPotential n σ p : E → ℝ) x))
      {x : E | x ≠ 0} := by
  apply (contDiffOn_radialSourceFlux (E := E) n σ).congr
  intro x hx
  exact pFlux_gradient_fundamentalPotential_all_p n hσ hp hx

end General

theorem classicalDivergence_pFlux_gradient_fundamentalPotential_all_p
    (n : ℕ) {σ p : ℝ} (hσ : 0 < σ) (hp : 1 < p)
    {x : Space n} (hx : x ≠ 0) :
    classicalDivergence
      (fun y : Space n => pFlux p (gradient (fundamentalPotential n σ p) y)) x = 0 := by
  have heq : (fun y : Space n => pFlux p (gradient (fundamentalPotential n σ p) y))
      =ᶠ[𝓝 x] radialSourceFlux n σ := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact pFlux_gradient_fundamentalPotential_all_p n hσ hp hy
  calc
    classicalDivergence
        (fun y : Space n => pFlux p (gradient (fundamentalPotential n σ p) y)) x =
        classicalDivergence (radialSourceFlux n σ) x := by
      unfold classicalDivergence
      rw [heq.fderiv_eq]
    _ = 0 := classicalDivergence_radialSourceFlux n σ (by simp [Space]) hx

/-- Genuine full-W0 weak harmonicity of the actual radial primitive off its
pole, with actual local Sobolev membership derived, for all p>1. -/
theorem weakPHarmonicPair_fundamentalPotential_all_p (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hp : 1 < p) :
    WeakPHarmonicPair p {x : Space n | x ≠ 0}
      (fundamentalPotential n σ p) (gradient (fundamentalPotential n σ p)) := by
  apply weakPHarmonicPair_of_classicalDivergence_eq_zero hp isOpen_ne
    (locallySobolevPair_fundamentalPotential n σ p hp)
    (contDiffOn_pFlux_gradient_fundamentalPotential_all_p n hσ hp)
  intro x hx
  exact classicalDivergence_pFlux_gradient_fundamentalPotential_all_p n hσ hp hx

/-- The radial primitive is strictly increasing at positive radii in all
three exponent regimes. Its negative coefficient is handled explicitly when
p<n; monotonicity is not postulated as a barrier hypothesis. -/
theorem strictMonoOn_fundamentalRadialValue_all_p (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hp : 1 < p) :
    StrictMonoOn (fundamentalRadialValue n σ p) (Ioi 0) := by
  intro r hr s hs hrs
  change 0 < r at hr
  change 0 < s at hs
  by_cases hpn : p = (n : ℝ)
  · subst p
    simp only [fundamentalRadialValue, fundamentalPotential,ite_true,
      criticalRadialPotential, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hs]
    have hm := mul_lt_mul_of_pos_left (Real.log_lt_log hr hrs)
      (Real.rpow_pos_of_pos hσ (-((n : ℝ) - 1)⁻¹))
    linarith
  · have hden : 0 < p - 1 := sub_pos.mpr hp
    have hq : (p - (n : ℝ)) / (p - 1) ≠ 0 :=
      div_ne_zero (sub_ne_zero.mpr hpn) hden.ne'
    simp only [fundamentalRadialValue, fundamentalPotential, if_neg hpn,
      radialPowerPotential, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hs]
    rcases lt_or_gt_of_ne hq with hneg | hpos
    · exact mul_lt_mul_of_neg_left (Real.rpow_lt_rpow_of_neg hr hrs hneg)
        (mul_neg_of_neg_of_pos (inv_lt_zero.mpr hneg)
          (Real.rpow_pos_of_pos hσ _))
    · exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hr.le hrs hpos)
        (mul_pos (inv_pos.mpr hpos) (Real.rpow_pos_of_pos hσ _))

end BMCompactPDE
end
end V5SegmentRadialBarrierFoundation


/-! Exact development proof segment: OptimizerFirstOrder -/
section V5SegmentOptimizerFirstOrder

/-! The actual conclusion of source Lemma7.1 from continuity and first-order
touching calculus. A strict unequal pair gives a local plateau lower bound
for the actual envelope. A zero endpoint derivative forces the test derivative
zero by the actual first-variation inequality. Neither Hopf nor a maximum
principle is postulated. General p-harmonic C1 regularity remains separate. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace BMCompactAnalytic

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem product_touching_first_order {t : ℝ} {v₁ v₂ φ : E → ℝ}
    {x y z : E} {m : ℝ} (hx : x = t • y + (1-t) • z)
    (hu : ∀ q, v₁ q ≤ m)
    (hupper : ∀ᶠ p in 𝓝 x, BMCompactEnvelope.supConvolution t v₁ v₂ p ≤ φ p) :
    ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2) := by
  have hcont : Continuous (fun q : E × E => t • q.1 + (1-t) • q.2) :=
    (continuous_fst.const_smul t).add (continuous_snd.const_smul (1-t))
  have hp : Tendsto (fun q : E × E => t • q.1 + (1-t) • q.2)
      (𝓝 (y,z)) (𝓝 x) := by
    simpa only [←hx] using (hcont.continuousAt (x := (y,z))).tendsto
  filter_upwards [hp.eventually hupper] with q hq
  exact (BMCompactEnvelope.min_le_supConvolution_of_decomposition t hu rfl).trans hq


theorem upperTest_isLocalMin_of_left_strict {t : ℝ} (ht : t ≠ 0)
    {v₁ v₂ φ : E → ℝ} {y z x : E} {m : ℝ}
    (hx : x = t • y + (1-t) • z) (hub : ∀ q, v₁ q ≤ m)
    (hc : ContinuousAt v₁ y) (hstrict : v₂ z < v₁ y)
    (hbase : φ x = v₂ z)
    (hupper : ∀ᶠ q in 𝓝 x, BMCompactEnvelope.supConvolution t v₁ v₂ q ≤ φ q) :
    IsLocalMin φ x := by
  let Y : E → E := fun q => t⁻¹ • (q - (1-t) • z)
  have hYx : Y x = y := by
    simp only [Y,hx,add_sub_cancel_right,smul_smul,inv_mul_cancel₀ ht,one_smul]
  have hY : Tendsto Y (𝓝 x) (𝓝 y) := by
    have hcont : Continuous Y := (continuous_id.sub continuous_const).const_smul t⁻¹
    simpa only [hYx] using (hcont.continuousAt (x := x)).tendsto
  have hval : ∀ᶠ q in 𝓝 x, v₂ z < v₁ (Y q) :=
    (hc.tendsto.comp hY).eventually (eventually_gt_nhds hstrict)
  filter_upwards [hupper,hval] with q hq hv
  have hblend : q = t • Y q + (1-t) • z := by
    dsimp [Y]
    rw [smul_smul,mul_inv_cancel₀ ht,one_smul,sub_add_cancel]
  rw [hbase]
  calc
    v₂ z = min (v₁ (Y q)) (v₂ z) := (min_eq_right hv.le).symm
    _ ≤ BMCompactEnvelope.supConvolution t v₁ v₂ q :=
      BMCompactEnvelope.min_le_supConvolution_of_decomposition t hub hblend
    _ ≤ φ q := hq

theorem upperTest_isLocalMin_of_right_strict {t : ℝ} (ht : 1-t ≠ 0)
    {v₁ v₂ φ : E → ℝ} {y z x : E} {m : ℝ}
    (hx : x = t • y + (1-t) • z) (hub : ∀ q, v₁ q ≤ m)
    (hc : ContinuousAt v₂ z) (hstrict : v₁ y < v₂ z)
    (hbase : φ x = v₁ y)
    (hupper : ∀ᶠ q in 𝓝 x, BMCompactEnvelope.supConvolution t v₁ v₂ q ≤ φ q) :
    IsLocalMin φ x := by
  let Z : E → E := fun q => (1-t)⁻¹ • (q - t • y)
  have hZx : Z x = z := by
    have he : t • y + (1-t) • z - t • y = (1-t) • z := by abel
    simp only [Z,hx,he,smul_smul,inv_mul_cancel₀ ht,one_smul]
  have hZ : Tendsto Z (𝓝 x) (𝓝 z) := by
    have hcont : Continuous Z := (continuous_id.sub continuous_const).const_smul (1-t)⁻¹
    simpa only [hZx] using (hcont.continuousAt (x := x)).tendsto
  have hval : ∀ᶠ q in 𝓝 x, v₁ y < v₂ (Z q) :=
    (hc.tendsto.comp hZ).eventually (eventually_gt_nhds hstrict)
  filter_upwards [hupper,hval] with q hq hv
  have hblend : q = t • y + (1-t) • Z q :=
    (BMCompactEnvelope.solved_blend t ht q y).symm
  rw [hbase]
  calc
    v₁ y = min (v₁ y) (v₂ (Z q)) := (min_eq_left hv.le).symm
    _ ≤ BMCompactEnvelope.supConvolution t v₁ v₂ q :=
      BMCompactEnvelope.min_le_supConvolution_of_decomposition t hub hblend
    _ ≤ φ q := hq

theorem touching_fderiv_eq_zero_of_left_zero {t : ℝ} (ht : 0 < t)
    {v₁ v₂ φ : E → ℝ} {y z x : E} {L₁ L₂ L : E →L[ℝ] ℝ}
    (hx : x = t • y + (1-t) • z)
    (h₁ : HasFDerivAt v₁ L₁ y) (h₂ : HasFDerivAt v₂ L₂ z)
    (hφ : HasFDerivAt φ L x) (hzero : L₁ = 0)
    (hv₁ : v₁ y = φ x) (hv₂ : v₂ z = φ x)
    (htouch : ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2)) : L = 0 := by
  have hfirst := touching_first_variation hx h₁ h₂ hφ hv₁ hv₂ htouch
  ext e
  have hpos := hfirst e 0
  have hneg := hfirst (-e) 0
  simp only [hzero,map_zero,zero_apply,min_self,smul_zero,add_zero,
    map_smul,smul_eq_mul,map_neg,neg_zero] at hpos hneg
  change L e = 0
  nlinarith

theorem touching_fderiv_eq_zero_of_right_zero {t : ℝ} (ht : t < 1)
    {v₁ v₂ φ : E → ℝ} {y z x : E} {L₁ L₂ L : E →L[ℝ] ℝ}
    (hx : x = t • y + (1-t) • z)
    (h₁ : HasFDerivAt v₁ L₁ y) (h₂ : HasFDerivAt v₂ L₂ z)
    (hφ : HasFDerivAt φ L x) (hzero : L₂ = 0)
    (hv₁ : v₁ y = φ x) (hv₂ : v₂ z = φ x)
    (htouch : ∀ᶠ q : E × E in 𝓝 (y,z),
      min (v₁ q.1) (v₂ q.2) ≤ φ (t • q.1 + (1-t) • q.2)) : L = 0 := by
  have hfirst := touching_first_variation hx h₁ h₂ hφ hv₁ hv₂ htouch
  ext e
  have hpos := hfirst 0 e
  have hneg := hfirst 0 (-e)
  simp only [hzero,map_zero,zero_apply,min_self,smul_zero,zero_add,
    map_smul,smul_eq_mul,map_neg,neg_zero] at hpos hneg
  change L e = 0
  nlinarith

end Normed

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_eq_zero_of_isLocalMin {φ : E → ℝ} {x : E} (h : IsLocalMin φ x) :
    gradient φ x = 0 := by
  unfold gradient
  rw [h.fderiv_eq_zero,map_zero]

theorem fderiv_eq_zero_of_gradient_eq_zero {f : E → ℝ} {x : E}
    (h : gradient f x = 0) : fderiv ℝ f x = 0 := by
  apply (InnerProductSpace.toDual ℝ E).symm.injective
  simpa only [gradient,map_zero] using h

/-- Balance needs continuity at the optimizing endpoints, even if the
larger-valued endpoint is on a saturated set and is not differentiable. -/
theorem supConvolution_optimizer_balanced
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {v₁ v₂ φ : E → ℝ} {y z x : E} {m : ℝ}
    (hx : x = t • y + (1-t) • z) (hub : ∀ q, v₁ q ≤ m)
    (hc₁ : ContinuousAt v₁ y) (hc₂ : ContinuousAt v₂ z)
    (hopt : BMCompactEnvelope.supConvolution t v₁ v₂ x = min (v₁ y) (v₂ z))
    (hcontact : BMCompactEnvelope.supConvolution t v₁ v₂ x = φ x)
    (hupper : ∀ᶠ q in 𝓝 x, BMCompactEnvelope.supConvolution t v₁ v₂ q ≤ φ q)
    (hgφ : gradient φ x ≠ 0) : v₁ y = v₂ z := by
  have hbase : φ x = min (v₁ y) (v₂ z) := hcontact.symm.trans hopt
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · apply hgφ
    apply gradient_eq_zero_of_isLocalMin
    exact upperTest_isLocalMin_of_right_strict (sub_pos.mpr ht1).ne' hx hub
      hc₂ hlt (hbase.trans (min_eq_left hlt.le)) hupper
  · apply hgφ
    apply gradient_eq_zero_of_isLocalMin
    exact upperTest_isLocalMin_of_left_strict ht.ne' hx hub
      hc₁ hgt (hbase.trans (min_eq_right hgt.le)) hupper

/-- Actual attained optimizing pairs of a nonzero-gradient upper test are
automatically balanced and noncritical. This proves the conclusion needed
from source Lemma7.1 using elementary first-order calculus, without invoking
an unformalized strong maximum principle or Hopf lemma. -/
theorem supConvolution_optimizer_balanced_noncritical
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {v₁ v₂ φ : E → ℝ} {y z x : E} {m : ℝ}
    (hx : x = t • y + (1-t) • z) (hub : ∀ q, v₁ q ≤ m)
    (h₁ : DifferentiableAt ℝ v₁ y) (h₂ : DifferentiableAt ℝ v₂ z)
    (hφ : DifferentiableAt ℝ φ x)
    (hopt : BMCompactEnvelope.supConvolution t v₁ v₂ x = min (v₁ y) (v₂ z))
    (hcontact : BMCompactEnvelope.supConvolution t v₁ v₂ x = φ x)
    (hupper : ∀ᶠ q in 𝓝 x, BMCompactEnvelope.supConvolution t v₁ v₂ q ≤ φ q)
    (hgφ : gradient φ x ≠ 0) :
    v₁ y = v₂ z ∧ gradient v₁ y ≠ 0 ∧ gradient v₂ z ≠ 0 := by
  have hbase : φ x = min (v₁ y) (v₂ z) := hcontact.symm.trans hopt
  have hbal : v₁ y = v₂ z := supConvolution_optimizer_balanced ht ht1 hx hub
    h₁.continuousAt h₂.continuousAt hopt hcontact hupper hgφ
  have hv₁ : v₁ y = φ x := (hbase.trans (min_eq_left hbal.le)).symm
  have hv₂ : v₂ z = φ x := hbal.symm.trans hv₁
  have htouch := product_touching_first_order hx hub hupper
  refine ⟨hbal,?_,?_⟩
  · intro hzero
    have hz := touching_fderiv_eq_zero_of_left_zero ht hx h₁.hasFDerivAt h₂.hasFDerivAt
      hφ.hasFDerivAt (fderiv_eq_zero_of_gradient_eq_zero hzero) hv₁ hv₂ htouch
    apply hgφ
    unfold gradient
    rw [hz,map_zero]
  · intro hzero
    have hz := touching_fderiv_eq_zero_of_right_zero ht1 hx h₁.hasFDerivAt h₂.hasFDerivAt
      hφ.hasFDerivAt (fderiv_eq_zero_of_gradient_eq_zero hzero) hv₁ hv₂ htouch
    apply hgφ
    unfold gradient
    rw [hz,map_zero]

/-- Source Lemma7.1's needed conclusion with regularity only below the
saturation level. Continuity first proves balance, so differentiability is
never demanded at a potentially saturated, larger-valued endpoint. -/
theorem supConvolution_optimizer_nondegenerate_below_level
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {v₁ v₂ φ : E → ℝ} {y z x : E} {m : ℝ}
    (hx : x = t • y + (1-t) • z) (hub : ∀ q, v₁ q ≤ m)
    (hc₁ : Continuous v₁) (hc₂ : Continuous v₂)
    (hreg₁ : ∀ q, v₁ q < m → DifferentiableAt ℝ v₁ q)
    (hreg₂ : ∀ q, v₂ q < m → DifferentiableAt ℝ v₂ q)
    (hφ : DifferentiableAt ℝ φ x)
    (hopt : BMCompactEnvelope.supConvolution t v₁ v₂ x = min (v₁ y) (v₂ z))
    (hcontact : BMCompactEnvelope.supConvolution t v₁ v₂ x = φ x)
    (hupper : ∀ᶠ q in 𝓝 x, BMCompactEnvelope.supConvolution t v₁ v₂ q ≤ φ q)
    (hsubtop : BMCompactEnvelope.supConvolution t v₁ v₂ x < m)
    (hgφ : gradient φ x ≠ 0) :
    v₁ y = v₂ z ∧ gradient v₁ y ≠ 0 ∧ gradient v₂ z ≠ 0 := by
  have hbal := supConvolution_optimizer_balanced ht ht1 hx hub hc₁.continuousAt
    hc₂.continuousAt hopt hcontact hupper hgφ
  have hv₁ : BMCompactEnvelope.supConvolution t v₁ v₂ x = v₁ y :=
    hopt.trans (min_eq_left hbal.le)
  have hv₂ : BMCompactEnvelope.supConvolution t v₁ v₂ x = v₂ z := hv₁.trans hbal
  exact supConvolution_optimizer_balanced_noncritical ht ht1 hx hub
    (hreg₁ y (hv₁ ▸ hsubtop)) (hreg₂ z (hv₂ ▸ hsubtop)) hφ hopt hcontact hupper hgφ

end Hilbert
end BMCompactAnalytic
end
end V5SegmentOptimizerFirstOrder


/-! Exact development proof segment: EnvelopeViscosity -/
section V5SegmentEnvelopeViscosity

/-! The actual supremal min-convolution satisfies the actual viscosity
p-Laplace inequality under the displayed component regularity/classical
equations. Balance and noncritical endpoints are derived, not assumed.
General weak-solution regularity and the capacity comparison remain separate. -/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology ContDiff
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem viscosity_supConvolution_of_attainment
    {p t m : ℝ} (hp : 1 < p) (ht : 0 < t) (ht1 : t < 1)
    {u v : E → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hub : ∀ x, u x ≤ m)
    (hC1u : ∀ x, u x < m → DifferentiableAt ℝ u x)
    (hC1v : ∀ x, v x < m → DifferentiableAt ℝ v x)
    (hC2u : ∀ x, u x < m → gradient u x ≠ 0 → ContDiffAt ℝ 2 u x)
    (hC2v : ∀ x, v x < m → gradient v x ≠ 0 → ContDiffAt ℝ 2 v x)
    (hPu : ∀ x, u x < m → gradient u x ≠ 0 → classicalPLaplacian p u x = 0)
    (hPv : ∀ x, v x < m → gradient v x ≠ 0 → classicalPLaplacian p v x = 0)
    (hcontinuous : Continuous (BMCompactEnvelope.supConvolution t u v))
    (hatt : ∀ x, ∃ y z : E, x = t • y + (1-t) • z ∧
      BMCompactEnvelope.supConvolution t u v x = min (u y) (v z)) :
    IsViscosityPSubsolution p {x | BMCompactEnvelope.supConvolution t u v x < m}
      (BMCompactEnvelope.supConvolution t u v) := by
  refine ⟨hp,isOpen_lt hcontinuous continuous_const,
    hcontinuous.continuousOn.upperSemicontinuousOn,?_⟩
  intro x hx φ hφ hcontact hupper hgφ
  have hx' : BMCompactEnvelope.supConvolution t u v x < m := hx
  obtain ⟨y,z,hxyz,hopt⟩ := hatt x
  obtain ⟨hbal,hgu,hgv⟩ := supConvolution_optimizer_nondegenerate_below_level ht ht1
    hxyz hub hu hv hC1u hC1v (hφ.differentiableAt (by norm_num))
    hopt hcontact hupper hx' hgφ
  have huval : BMCompactEnvelope.supConvolution t u v x = u y :=
    hopt.trans (min_eq_left hbal.le)
  have hvval : BMCompactEnvelope.supConvolution t u v x = v z := huval.trans hbal
  have hult : u y < m := huval ▸ hx'
  have hvlt : v z < m := hvval ▸ hx'
  have htouch := supConvolution_local_touching hxyz hub hupper
  have hL := local_touching_normalizedPLaplacian_nonneg hp ht ht1 hxyz
    (hC2u y hult hgu) (hC2v z hvlt hgv) hφ hgu hgv
    (huval.symm.trans hcontact) (hvval.symm.trans hcontact) htouch
    (hPu y hult hgu) (hPv z hvlt hgv)
  exact hL.2

section Proper
variable [ProperSpace E]

/-- Printed Lemma7.2's actual envelope-viscosity conclusion in the positive
decaying regime. Attainment/continuity, endpoint balance and noncriticality
are all proved. Component C1/C2/classical equations remain explicit. -/
theorem viscosity_supConvolution_subcritical
    {p t m : ℝ} (hp : 1 < p) (ht : 0 < t) (ht1 : t < 1)
    {u v : E → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu0 : ∀ x, 0 < u x) (hv0 : ∀ x, 0 < v x)
    (hulim : Tendsto u (cobounded E) (𝓝 0))
    (hub : ∀ x, u x ≤ m)
    (hC1u : ∀ x, u x < m → DifferentiableAt ℝ u x)
    (hC1v : ∀ x, v x < m → DifferentiableAt ℝ v x)
    (hC2u : ∀ x, u x < m → gradient u x ≠ 0 → ContDiffAt ℝ 2 u x)
    (hC2v : ∀ x, v x < m → gradient v x ≠ 0 → ContDiffAt ℝ 2 v x)
    (hPu : ∀ x, u x < m → gradient u x ≠ 0 → classicalPLaplacian p u x = 0)
    (hPv : ∀ x, v x < m → gradient v x ≠ 0 → classicalPLaplacian p v x = 0) :
    IsViscosityPSubsolution p {x | BMCompactEnvelope.supConvolution t u v x < m}
      (BMCompactEnvelope.supConvolution t u v) := by
  have htne : 1-t ≠ 0 := (sub_pos.mpr ht1).ne'
  exact viscosity_supConvolution_of_attainment hp ht ht1 hu hv hub hC1u hC1v hC2u hC2v
    hPu hPv
    (BMCompactEnvelope.continuous_supConvolution_subcritical t htne hu hv hu0 hv0 hulim)
    (BMCompactEnvelope.exists_optimalPair_subcritical t htne hu hv hu0 hv0 hulim)

/-- The corresponding actual envelope-viscosity conclusion in the
negative-infinity regime used for critical/supercritical Green functions. -/
theorem viscosity_supConvolution_atBot
    {p t m : ℝ} (hp : 1 < p) (ht : 0 < t) (ht1 : t < 1)
    {u v : E → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hulim : Tendsto u (cobounded E) atBot)
    (hub : ∀ x, u x ≤ m)
    (hC1u : ∀ x, u x < m → DifferentiableAt ℝ u x)
    (hC1v : ∀ x, v x < m → DifferentiableAt ℝ v x)
    (hC2u : ∀ x, u x < m → gradient u x ≠ 0 → ContDiffAt ℝ 2 u x)
    (hC2v : ∀ x, v x < m → gradient v x ≠ 0 → ContDiffAt ℝ 2 v x)
    (hPu : ∀ x, u x < m → gradient u x ≠ 0 → classicalPLaplacian p u x = 0)
    (hPv : ∀ x, v x < m → gradient v x ≠ 0 → classicalPLaplacian p v x = 0) :
    IsViscosityPSubsolution p {x | BMCompactEnvelope.supConvolution t u v x < m}
      (BMCompactEnvelope.supConvolution t u v) := by
  have htne : 1-t ≠ 0 := (sub_pos.mpr ht1).ne'
  exact viscosity_supConvolution_of_attainment hp ht ht1 hu hv hub hC1u hC1v hC2u hC2v
    hPu hPv
    (BMCompactEnvelope.continuous_supConvolution_atBot t htne hu hv hulim)
    (BMCompactEnvelope.exists_optimalPair_atBot t htne hu hv hulim)

end Proper
end BMCompactAnalytic
end
end V5SegmentEnvelopeViscosity


/-! Exact development proof segment: WeakViscosityBridge -/
section V5SegmentWeakViscosityBridge

/-! A genuine weak-to-viscosity bridge with explicit analytic regularity:
C1 on the domain and C2 only at noncritical points. No regularity theorem
for arbitrary weak solutions is assumed as a checked mathematical fact. -/
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactPDE

theorem WeakPHarmonicPair.classicalPLaplacian_eq_zero_of_contDiffAt_two
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : WeakPHarmonicPair p Ω u (gradient u)) {x : Space n}
    (hx : x ∈ Ω) (hu : ContDiffAt ℝ 2 u x) (hg : gradient u x ≠ 0) :
    BMCompactAnalytic.classicalPLaplacian p u x = 0 := by
  obtain ⟨U,hUn,huU⟩ := hu.contDiffOn le_rfl (by simp)
  obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hUn
  have hW := hw.mono (U := Ω ∩ V) inter_subset_left (hw.2.1.inter hV)
  exact hW.classicalPLaplacian_eq_zero_at
    (huU.mono (inter_subset_right.trans hVU)) ⟨hx,hxV⟩ hg

theorem IsWeakPHarmonic.classicalPLaplacian_eq_zero_of_contDiffAt_two
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : IsWeakPHarmonic p Ω u) {x : Space n}
    (hx : x ∈ Ω) (hu : ContDiffAt ℝ 2 u x) (hg : gradient u x ≠ 0) :
    BMCompactAnalytic.classicalPLaplacian p u x = 0 := by
  obtain ⟨U,hUn,huU⟩ := hu.contDiffOn le_rfl (by simp)
  obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hUn
  obtain ⟨g,hw⟩ := hw
  have hW : IsWeakPHarmonic p (Ω ∩ V) u :=
    ⟨g,hw.mono inter_subset_left (hw.2.1.inter hV)⟩
  exact hW.classicalPLaplacian_eq_zero_at
    (huU.mono (inter_subset_right.trans hVU)) ⟨hx,hxV⟩ hg

/-- The classical endpoint equation is derived from the actual weak equation;
zero-gradient points require only C1 and the test's first-order contact. -/
theorem IsWeakPHarmonic.viscosity_of_C1_noncritical_C2
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : IsWeakPHarmonic p Ω u) (hu : ContDiffOn ℝ 1 u Ω)
    (hreg : ∀ x ∈ Ω, gradient u x ≠ 0 → ContDiffAt ℝ 2 u x) :
    BMCompactAnalytic.IsViscosityPSubsolution p Ω u := by
  obtain ⟨g,hg⟩ := hw
  have hw' : IsWeakPHarmonic p Ω u := ⟨g,hg⟩
  refine ⟨hg.1,hg.2.1,hu.continuousOn.upperSemicontinuousOn,?_⟩
  intro x hx φ hφ hv htouch hgradφ
  have hdu := (hu.contDiffAt (hg.2.1.mem_nhds hx)).differentiableAt (by norm_num)
  have hsame := BMCompactAnalytic.gradient_eq_of_local_upper_contact
    hdu (hφ.differentiableAt (by norm_num)) hv htouch
  have hgrad : gradient u x ≠ 0 := by rwa [hsame]
  have hu2 := hreg x hx hgrad
  have hP := hw'.classicalPLaplacian_eq_zero_of_contDiffAt_two hx hu2 hgrad
  have hN := BMCompactAnalytic.normalizedPLaplacian_eq_zero_of_classical_eq_zero hgrad hP
  have hle := BMCompactAnalytic.normalizedPLaplacian_le_of_local_upper_contact
    hg.1 hu2 hφ hv htouch hgradφ
  rwa [hN] at hle

theorem IsWeakPHarmonic.manuscriptViscosity_of_C1_noncritical_C2
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : IsWeakPHarmonic p Ω u) (hu : ContDiffOn ℝ 1 u Ω)
    (hreg : ∀ x ∈ Ω, gradient u x ≠ 0 → ContDiffAt ℝ 2 u x) :
    BMCompactAnalytic.IsManuscriptViscosityPSubsolution p Ω u :=
  (hw.viscosity_of_C1_noncritical_C2 hu hreg).manuscript

end BMCompactPDE
end
end V5SegmentWeakViscosityBridge


/-! Exact development proof segment: WeakEnvelopeViscosity -/
section V5SegmentWeakEnvelopeViscosity

/-! The actual weak equations replace the classical equation hypotheses in
the actual envelope viscosity theorem. Endpoint balance/noncriticality,
pointwise classical equations, and viscosity tests are all derived. Component
regularity and general potential existence are not proved by these wrappers. -/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology ContDiff
namespace BMCompactAnalytic
open BMCompactPDE
variable {n : ℕ}

theorem weak_viscosity_supConvolution_of_attainment
    {p t m : ℝ} (hp : 1 < p) (ht : 0 < t) (ht1 : t < 1)
    {u v : Space n → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hub : ∀ x, u x ≤ m)
    (hC1u : ∀ x, u x < m → DifferentiableAt ℝ u x)
    (hC1v : ∀ x, v x < m → DifferentiableAt ℝ v x)
    (hC2u : ∀ x, u x < m → gradient u x ≠ 0 → ContDiffAt ℝ 2 u x)
    (hC2v : ∀ x, v x < m → gradient v x ≠ 0 → ContDiffAt ℝ 2 v x)
    (hwu : IsWeakPHarmonic p {x | u x < m} u)
    (hwv : IsWeakPHarmonic p {x | v x < m} v)
    (hcontinuous : Continuous (BMCompactEnvelope.supConvolution t u v))
    (hatt : ∀ x, ∃ y z : Space n, x = t • y + (1-t) • z ∧
      BMCompactEnvelope.supConvolution t u v x = min (u y) (v z)) :
    IsViscosityPSubsolution p {x | BMCompactEnvelope.supConvolution t u v x < m}
      (BMCompactEnvelope.supConvolution t u v) := by
  apply viscosity_supConvolution_of_attainment hp ht ht1 hu hv hub hC1u hC1v hC2u hC2v
  · intro x hx hg
    exact hwu.classicalPLaplacian_eq_zero_of_contDiffAt_two hx (hC2u x hx hg) hg
  · intro x hx hg
    exact hwv.classicalPLaplacian_eq_zero_of_contDiffAt_two hx (hC2v x hx hg) hg
  · exact hcontinuous
  · exact hatt

section Proper

/-- Printed Lemma7.2's actual envelope-viscosity conclusion in the positive
decaying regime. Attainment/continuity, endpoint balance and noncriticality
are all proved. Component regularity and actual weak equations remain explicit. -/
theorem weak_viscosity_supConvolution_subcritical
    {p t m : ℝ} (hp : 1 < p) (ht : 0 < t) (ht1 : t < 1)
    {u v : Space n → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu0 : ∀ x, 0 < u x) (hv0 : ∀ x, 0 < v x)
    (hulim : Tendsto u (cobounded (Space n)) (𝓝 0))
    (hub : ∀ x, u x ≤ m)
    (hC1u : ∀ x, u x < m → DifferentiableAt ℝ u x)
    (hC1v : ∀ x, v x < m → DifferentiableAt ℝ v x)
    (hC2u : ∀ x, u x < m → gradient u x ≠ 0 → ContDiffAt ℝ 2 u x)
    (hC2v : ∀ x, v x < m → gradient v x ≠ 0 → ContDiffAt ℝ 2 v x)
    (hwu : IsWeakPHarmonic p {x | u x < m} u)
    (hwv : IsWeakPHarmonic p {x | v x < m} v) :
    IsViscosityPSubsolution p {x | BMCompactEnvelope.supConvolution t u v x < m}
      (BMCompactEnvelope.supConvolution t u v) := by
  have htne : 1-t ≠ 0 := (sub_pos.mpr ht1).ne'
  exact weak_viscosity_supConvolution_of_attainment hp ht ht1 hu hv hub hC1u hC1v hC2u hC2v
    hwu hwv
    (BMCompactEnvelope.continuous_supConvolution_subcritical t htne hu hv hu0 hv0 hulim)
    (BMCompactEnvelope.exists_optimalPair_subcritical t htne hu hv hu0 hv0 hulim)

/-- The corresponding actual envelope-viscosity conclusion in the
negative-infinity regime used for critical/supercritical Green functions. -/
theorem weak_viscosity_supConvolution_atBot
    {p t m : ℝ} (hp : 1 < p) (ht : 0 < t) (ht1 : t < 1)
    {u v : Space n → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hulim : Tendsto u (cobounded (Space n)) atBot)
    (hub : ∀ x, u x ≤ m)
    (hC1u : ∀ x, u x < m → DifferentiableAt ℝ u x)
    (hC1v : ∀ x, v x < m → DifferentiableAt ℝ v x)
    (hC2u : ∀ x, u x < m → gradient u x ≠ 0 → ContDiffAt ℝ 2 u x)
    (hC2v : ∀ x, v x < m → gradient v x ≠ 0 → ContDiffAt ℝ 2 v x)
    (hwu : IsWeakPHarmonic p {x | u x < m} u)
    (hwv : IsWeakPHarmonic p {x | v x < m} v) :
    IsViscosityPSubsolution p {x | BMCompactEnvelope.supConvolution t u v x < m}
      (BMCompactEnvelope.supConvolution t u v) := by
  have htne : 1-t ≠ 0 := (sub_pos.mpr ht1).ne'
  exact weak_viscosity_supConvolution_of_attainment hp ht ht1 hu hv hub hC1u hC1v hC2u hC2v
    hwu hwv
    (BMCompactEnvelope.continuous_supConvolution_atBot t htne hu hv hulim)
    (BMCompactEnvelope.exists_optimalPair_atBot t htne hu hv hulim)

end Proper
end BMCompactAnalytic
end
end V5SegmentWeakEnvelopeViscosity


/-! Exact development proof segment: AnnularHopf -/
section V5SegmentAnnularHopf

/-! Actual normalized annular barriers for every p>1. A genuine globally
smooth extension removes the pole before applying actual C1
weak comparison theorem. This does not postulate a Hopf or maximum principle. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

def annularBarrierDenominator (n : ℕ) (p r R : ℝ) : ℝ :=
  fundamentalRadialValue n 1 p R - fundamentalRadialValue n 1 p r

def annularRadialBarrier (n : ℕ) (p r R : ℝ) (x : Space n) : ℝ :=
  (fundamentalRadialValue n 1 p R - fundamentalPotential n 1 p x) /
    annularBarrierDenominator n p r R

theorem annularBarrierDenominator_pos (n : ℕ) {p r R : ℝ}
    (hp : 1 < p) (hr : 0 < r) (hrR : r < R) :
    0 < annularBarrierDenominator n p r R :=
  sub_pos.mpr ((strictMonoOn_fundamentalRadialValue_all_p n zero_lt_one hp)
    hr (hr.trans hrR) hrR)

theorem annularRadialBarrier_zero_outer (n : ℕ) (p r R : ℝ)
    {x : Space n} (hx : ‖x‖ = R) : annularRadialBarrier n p r R x = 0 := by
  rw [annularRadialBarrier, ←fundamentalPotential_norm, hx, sub_self, zero_div]

theorem annularRadialBarrier_one_inner (n : ℕ) {p r R : ℝ}
    (hp : 1 < p) (hr : 0 < r) (hrR : r < R)
    {x : Space n} (hx : ‖x‖ = r) : annularRadialBarrier n p r R x = 1 := by
  rw [annularRadialBarrier, ←fundamentalPotential_norm, hx]
  exact div_self (annularBarrierDenominator_pos n hp hr hrR).ne'

theorem annularRadialBarrier_bounds (n : ℕ) {p r R : ℝ}
    (hp : 1 < p) (hr : 0 < r) (hrR : r < R)
    {x : Space n} (hxr : r ≤ ‖x‖) (hxR : ‖x‖ ≤ R) :
    0 ≤ annularRadialBarrier n p r R x ∧ annularRadialBarrier n p r R x ≤ 1 := by
  have hmono := (strictMonoOn_fundamentalRadialValue_all_p n zero_lt_one hp).monotoneOn
  have hpos : 0 < ‖x‖ := hr.trans_le hxr
  have hleft := hmono hr hpos hxr
  have hright := hmono hpos (hr.trans hrR) hxR
  rw [fundamentalPotential_norm] at hleft hright
  have hD := annularBarrierDenominator_pos n hp hr hrR
  constructor
  · exact div_nonneg (sub_nonneg.mpr hright) hD.le
  · apply (div_le_one hD).mpr
    dsimp [annularBarrierDenominator]
    linarith

theorem annularRadialBarrier_pos (n : ℕ) {p r R : ℝ}
    (hp : 1 < p) (hr : 0 < r) (hrR : r < R)
    {x : Space n} (hx : 0 < ‖x‖) (hxR : ‖x‖ < R) :
    0 < annularRadialBarrier n p r R x := by
  apply div_pos _ (annularBarrierDenominator_pos n hp hr hrR)
  apply sub_pos.mpr
  rw [←fundamentalPotential_norm]
  exact (strictMonoOn_fundamentalRadialValue_all_p n zero_lt_one hp) hx (hr.trans hrR) hxR

def flattenedRadialPrimitive (n : ℕ) (p : ℝ)
    (b : ContDiffBump (0 : Space n)) (x : Space n) : ℝ :=
  (1 - b x) * fundamentalPotential n 1 p x

theorem contDiff_flattenedRadialPrimitive (n : ℕ) (p : ℝ)
    (b : ContDiffBump (0 : Space n)) : ContDiff ℝ ∞ (flattenedRadialPrimitive n p b) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Space n => (0 : ℝ)) 0).congr_of_eventuallyEq
    filter_upwards [b.eventuallyEq_one] with y hy
    simp only [flattenedRadialPrimitive, Pi.one_apply] at *
    rw [hy, sub_self, zero_mul]
  · exact (contDiffAt_const.sub b.contDiff.contDiffAt).mul
      (contDiffAt_fundamentalPotential n 1 p hx)

theorem flattenedRadialPrimitive_eq (n : ℕ) (p : ℝ)
    (b : ContDiffBump (0 : Space n)) {x : Space n} (hx : b.rOut ≤ ‖x‖) :
    flattenedRadialPrimitive n p b x = fundamentalPotential n 1 p x := by
  have hb : b x = 0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
  simp only [flattenedRadialPrimitive, hb, sub_zero, one_mul]

theorem flattenedRadialPrimitive_eventuallyEq (n : ℕ) (p : ℝ)
    (b : ContDiffBump (0 : Space n)) {x : Space n} (hx : b.rOut < ‖x‖) :
    flattenedRadialPrimitive n p b =ᶠ[𝓝 x] fundamentalPotential n 1 p := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  exact flattenedRadialPrimitive_eq n p b hy.le

theorem WeakPHarmonicPair.congr_gradient_on {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hgh : EqOn g h Ω) :
    WeakPHarmonicPair p Ω u h := by
  refine ⟨hu.1,hu.2.1,?_,?_⟩
  · intro D hD
    apply (hu.2.2.1 D hD).congr EventuallyEq.rfl
    filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
    exact hgh (hD.2.2 (subset_closure hx))
  · intro D hD θ H hθ
    obtain ⟨hi,hzero⟩ := hu.2.2.2 D hD θ H hθ
    have heq : fluxPairing p g H =ᵐ[volume.restrict D] fluxPairing p h H := by
      filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
      simp only [fluxPairing,hgh (hD.2.2 (subset_closure hx))]
    exact ⟨hi.congr heq,(integral_congr_ae heq).symm.trans hzero⟩

theorem weakPHarmonicPair_flattenedRadialPrimitive (n : ℕ) {p : ℝ} (hp : 1 < p)
    (b : ContDiffBump (0 : Space n)) :
    WeakPHarmonicPair p {x : Space n | b.rOut < ‖x‖}
      (flattenedRadialPrimitive n p b) (gradient (flattenedRadialPrimitive n p b)) := by
  have hΩ : IsOpen {x : Space n | b.rOut < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hu := (weakPHarmonicPair_fundamentalPotential_all_p n zero_lt_one hp).mono
    (fun x hx => norm_ne_zero_iff.mp (ne_of_gt (b.rOut_pos.trans hx))) hΩ
  have hf : EqOn (fundamentalPotential n 1 p) (flattenedRadialPrimitive n p b)
      {x : Space n | b.rOut < ‖x‖} := by
    intro x hx
    exact (flattenedRadialPrimitive_eq n p b hx.le).symm
  apply (hu.congr_fun hf).congr_gradient_on
  intro x hx
  unfold gradient
  exact congrArg (InnerProductSpace.toDual ℝ (Space n)).symm
    (flattenedRadialPrimitive_eventuallyEq n p b hx).fderiv_eq.symm

def annularSmoothBarrier (n : ℕ) (p r R : ℝ)
    (b : ContDiffBump (0 : Space n)) (x : Space n) : ℝ :=
  (- (annularBarrierDenominator n p r R)⁻¹) * flattenedRadialPrimitive n p b x +
    (annularBarrierDenominator n p r R)⁻¹ * fundamentalRadialValue n 1 p R

theorem contDiff_annularSmoothBarrier (n : ℕ) (p r R : ℝ)
    (b : ContDiffBump (0 : Space n)) : ContDiff ℝ ∞ (annularSmoothBarrier n p r R b) :=
  (contDiff_const.mul (contDiff_flattenedRadialPrimitive n p b)).add contDiff_const

theorem annularSmoothBarrier_eq (n : ℕ) (p r R : ℝ)
    (b : ContDiffBump (0 : Space n)) {x : Space n} (hx : b.rOut ≤ ‖x‖) :
    annularSmoothBarrier n p r R b x = annularRadialBarrier n p r R x := by
  unfold annularSmoothBarrier
  rw [flattenedRadialPrimitive_eq n p b hx]
  unfold annularRadialBarrier
  ring

theorem weakPHarmonicPair_annularSmoothBarrier (n : ℕ) {p : ℝ} (hp : 1 < p)
    (r R : ℝ) (b : ContDiffBump (0 : Space n)) :
    WeakPHarmonicPair p {x : Space n | b.rOut < ‖x‖}
      (annularSmoothBarrier n p r R b) (gradient (annularSmoothBarrier n p r R b)) := by
  have hu := ((weakPHarmonicPair_flattenedRadialPrimitive n hp b).smul
    (-(annularBarrierDenominator n p r R)⁻¹)).add_const
      ((annularBarrierDenominator n p r R)⁻¹ * fundamentalRadialValue n 1 p R)
  apply hu.congr_gradient_on
  intro x hx
  have hadd : gradient (annularSmoothBarrier n p r R b) x =
      gradient (fun y => (-(annularBarrierDenominator n p r R)⁻¹) *
        flattenedRadialPrimitive n p b y) x := by
    unfold gradient annularSmoothBarrier
    rw [fderiv_add_const]
  rw [hadd,BMCompactCapacityV2.gradient_const_mul]
  rfl

def radialAnnulus (n : ℕ) (r R : ℝ) : Set (Space n) :=
  {x | r < ‖x‖ ∧ ‖x‖ < R}

theorem isOpen_radialAnnulus (n : ℕ) (r R : ℝ) : IsOpen (radialAnnulus n r R) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem isBounded_radialAnnulus (n : ℕ) (r R : ℝ) :
    Bornology.IsBounded (radialAnnulus n r R) := by
  apply (isBounded_ball (x := (0 : Space n)) (r := R)).subset
  intro x hx
  simpa only [mem_ball,dist_zero_right] using hx.2

theorem norm_of_mem_frontier_radialAnnulus (n : ℕ) (r R : ℝ) {x : Space n}
    (hx : x ∈ frontier (radialAnnulus n r R)) : ‖x‖ = r ∨ ‖x‖ = R := by
  have hclosed : IsClosed {x : Space n | r ≤ ‖x‖ ∧ ‖x‖ ≤ R} :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hsub : radialAnnulus n r R ⊆ {y : Space n | r ≤ ‖y‖ ∧ ‖y‖ ≤ R} :=
    fun y hy => ⟨hy.1.le,hy.2.le⟩
  have hbounds : r ≤ ‖x‖ ∧ ‖x‖ ≤ R :=
    (closure_minimal hsub hclosed) hx.1
  have hnot : x ∉ radialAnnulus n r R := by
    rw [(isOpen_radialAnnulus n r R).frontier_eq] at hx
    exact hx.2
  by_cases hr : ‖x‖ = r
  · exact Or.inl hr
  · right
    by_contra hR
    apply hnot
    exact ⟨lt_of_le_of_ne hbounds.1 (Ne.symm hr),lt_of_le_of_ne hbounds.2 hR⟩

/-- Actual annular weak comparison yields the explicit radial lower barrier
for globally C1 p-harmonic solutions, with ordinary two-sphere data.
No lower-barrier or normal-derivative conclusion is assumed. -/
theorem annularRadialBarrier_le_of_C1_weak_harmonic
    {n : ℕ} (hn : 2 ≤ n) {p r R m : ℝ} (hp : 1 < p)
    (hr : 0 < r) (hrR : r < R)
    {u : Space n → ℝ} (hu : ContDiff ℝ 1 u)
    (hP : WeakPHarmonicPair p (radialAnnulus n r R) u (gradient u))
    (hinner : ∀ x : Space n, ‖x‖ = r → m ≤ u x)
    (houter : ∀ x : Space n, ‖x‖ = R → 0 ≤ u x) :
    ∀ x ∈ radialAnnulus n r R, m * annularRadialBarrier n p r R x ≤ u x := by
  let b : ContDiffBump (0 : Space n) := ⟨r/4,r/2,by linarith,by linarith⟩
  have hb : b.rOut < r := by dsimp [b];linarith
  have hDsub : radialAnnulus n r R ⊆ {x : Space n | b.rOut < ‖x‖} :=
    fun x hx => hb.trans hx.1
  have hB := (weakPHarmonicPair_annularSmoothBarrier n hp r R b).mono
    hDsub (isOpen_radialAnnulus n r R)
  have hM := hB.smul m
  have hMgrad : WeakPHarmonicPair p (radialAnnulus n r R)
      (fun x => m * annularSmoothBarrier n p r R b x)
      (gradient (fun x => m * annularSmoothBarrier n p r R b x)) := by
    apply hM.congr_gradient_on
    intro x hx
    rw [BMCompactCapacityV2.gradient_const_mul]
    rfl
  have hbound : ∀ x ∈ frontier (radialAnnulus n r R),
      m * annularSmoothBarrier n p r R b x ≤ u x := by
    intro x hx
    rcases norm_of_mem_frontier_radialAnnulus n r R hx with hi | ho
    · rw [annularSmoothBarrier_eq n p r R b (by rw [hi];exact hb.le),
        annularRadialBarrier_one_inner n hp hr hrR hi,mul_one]
      exact hinner x hi
    · rw [annularSmoothBarrier_eq n p r R b (by rw [ho];exact (hb.trans hrR).le),
        annularRadialBarrier_zero_outer n p r R ho,mul_zero]
      exact houter x ho
  have hle := hMgrad.leOn_of_C1_boundary_order hP
    ((contDiff_const.mul (contDiff_annularSmoothBarrier n p r R b)).of_le (by simp)) hu hn
    (isBounded_radialAnnulus n r R) hbound
  intro x hx
  simpa only [annularSmoothBarrier_eq n p r R b (hDsub hx).le] using hle x hx

end BMCompactPDE


/-! A genuine quantitative Hopf conclusion in the globally C1 weak
p-harmonic subcase. The annular lower barrier is obtained by actual weak
comparison from two-sphere boundary data, then actual one-sided derivative
limits give a strictly positive inward derivative. General nonsmooth boundary
regularity and the arbitrary-domain strong maximum principle remain separate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem derivative_le_of_eventually_le_right {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0) (h0 : f 0 = g 0)
    (hle : ∀ᶠ s in 𝓝[>] (0 : ℝ), f s ≤ g s) : a ≤ b := by
  have hf' : Tendsto (fun s : ℝ => (f s - f 0) / s) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
    simpa only [zero_add,smul_eq_mul,div_eq_mul_inv,mul_comm] using hf.tendsto_slope_zero_right
  have hg' : Tendsto (fun s : ℝ => (g s - g 0) / s) (𝓝[>] (0 : ℝ)) (𝓝 b) := by
    simpa only [zero_add,smul_eq_mul,div_eq_mul_inv,mul_comm] using hg.tendsto_slope_zero_right
  apply le_of_tendsto_of_tendsto hf' hg'
  filter_upwards [hle,self_mem_nhdsWithin] with s hs hs0
  rw [h0]
  exact div_le_div_of_nonneg_right (sub_le_sub_right hs (g 0)) hs0.le

theorem inward_derivative_annularRadialBarrier
    (n : ℕ) {p r R : ℝ} (hp : 1 < p) (hR : 0 < R)
    {ν : Space n} (hν : ‖ν‖ = 1) :
    HasDerivAt (fun s : ℝ => annularRadialBarrier n p r R (R • ν - s • ν))
      ((R ^ ((p - (n : ℝ)) / (p - 1) - 2) * R) /
        annularBarrierDenominator n p r R) 0 := by
  have hxnorm : ‖R • ν‖ = R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,hν,mul_one]
  have hx : R • ν ≠ 0 := norm_ne_zero_iff.mp (by rw [hxnorm];exact hR.ne')
  have hpath : HasDerivAt (fun s : ℝ => R • ν - s • ν) (-ν) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_sub (R • ν)
  have hF := (hasGradientAt_fundamentalPotential_all_p n 1 hp hx).hasFDerivAt
  have hcomp := hF.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have hcoef : (toDual ℝ (Space n) (normalizedRadialGradient n 1 p (R • ν))) (-ν) =
      -(R ^ ((p - (n : ℝ)) / (p - 1) - 2) * R) := by
    rw [toDual_apply_apply]
    simp only [normalizedRadialGradient,Real.one_rpow,hxnorm,one_mul]
    rw [real_inner_smul_left,real_inner_smul_left,inner_neg_right,
      real_inner_self_eq_norm_sq,hν,one_pow]
    ring
  rw [hcoef] at hcomp
  have hd := (hcomp.const_sub (fundamentalRadialValue n 1 p R)).div_const
    (annularBarrierDenominator n p r R)
  simpa only [neg_neg,Function.comp_apply,annularRadialBarrier] using! hd

/-- The actual comparison lower bound implies the quantitative one-sided
Hopf inequality at a zero on the outer sphere. -/
theorem annular_inward_derivative_lower_bound
    {n : ℕ} {p r R m : ℝ} (hp : 1 < p) (hr : 0 < r) (hrR : r < R)
    {ν : Space n} (hν : ‖ν‖ = 1) {u : Space n → ℝ} {g : Space n}
    (hu : HasGradientAt u g (R • ν)) (hzero : u (R • ν) = 0)
    (hlower : ∀ x ∈ radialAnnulus n r R, m * annularRadialBarrier n p r R x ≤ u x) :
    m * ((R ^ ((p - (n : ℝ)) / (p - 1) - 2) * R) /
      annularBarrierDenominator n p r R) ≤ ⟪g,-ν⟫_ℝ := by
  have hR : 0 < R := hr.trans hrR
  have hpath : HasDerivAt (fun s : ℝ => R • ν - s • ν) (-ν) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ν).const_sub (R • ν)
  have hU := hu.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
  have hU' : HasDerivAt (fun s : ℝ => u (R • ν - s • ν)) ⟪g,-ν⟫_ℝ 0 := by
    simpa only [Function.comp_apply,toDual_apply_apply] using! hU
  have hB := (inward_derivative_annularRadialBarrier n (r := r) hp hR hν).const_mul m
  apply derivative_le_of_eventually_le_right hB hU'
  · have hxnorm : ‖R • ν‖ = R := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR,hν,mul_one]
    simp only [zero_smul,sub_zero,annularRadialBarrier_zero_outer n p r R hxnorm,
      mul_zero,hzero]
  · have he : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < R-r :=
      (eventually_lt_nhds (sub_pos.mpr hrR)).filter_mono nhdsWithin_le_nhds
    filter_upwards [he,self_mem_nhdsWithin] with s hs hs0
    have hspos : 0 < s := hs0
    apply hlower
    have hn : ‖R • ν - s • ν‖ = R-s := by
      rw [←sub_smul,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith),hν,mul_one]
    change r < ‖R • ν - s • ν‖ ∧ ‖R • ν - s • ν‖ < R
    rw [hn]
    constructor <;> linarith

/-- Quantitative Hopf in the globally C1 weak-solution subcase. Neither a
positive-part W0 test nor an annular barrier lower bound is a premise. -/
theorem C1_annular_hopf
    {n : ℕ} (hn : 2 ≤ n) {p r R m : ℝ} (hp : 1 < p)
    (hr : 0 < r) (hrR : r < R) (hm : 0 < m)
    {u : Space n → ℝ} (hu : ContDiff ℝ 1 u)
    (hP : WeakPHarmonicPair p (radialAnnulus n r R) u (gradient u))
    (hinner : ∀ x : Space n, ‖x‖ = r → m ≤ u x)
    (houter : ∀ x : Space n, ‖x‖ = R → 0 ≤ u x)
    {ν : Space n} (hν : ‖ν‖ = 1) (hzero : u (R • ν) = 0) :
    0 < ⟪gradient u (R • ν),-ν⟫_ℝ ∧ gradient u (R • ν) ≠ 0 := by
  have hlow := annularRadialBarrier_le_of_C1_weak_harmonic hn hp hr hrR hu hP hinner houter
  have hgrad := (hu.differentiable (by simp) (R • ν)).hasGradientAt
  have hb := annular_inward_derivative_lower_bound hp hr hrR hν hgrad hzero hlow
  have hpos : 0 < m * ((R ^ ((p - (n : ℝ)) / (p - 1) - 2) * R) /
      annularBarrierDenominator n p r R) :=
    mul_pos hm (div_pos (mul_pos (Real.rpow_pos_of_pos (hr.trans hrR) _) (hr.trans hrR))
      (annularBarrierDenominator_pos n hp hr hrR))
  have hpder : 0 < ⟪gradient u (R • ν),-ν⟫_ℝ := hpos.trans_le hb
  refine ⟨hpder,?_⟩
  intro hz
  simpa [hz] using hpder

/-- Hopf's nonzero inward derivative on a ball, in the actual globally
C1 weak p-harmonic subcase. Strict interior positivity supplies the
inner-sphere constant by compactness; no quantitative lower bound is assumed. -/
theorem C1_ball_hopf
    {n : ℕ} (hn : 2 ≤ n) {p R : ℝ} (hp : 1 < p) (hR : 0 < R)
    {u : Space n → ℝ} (hu : ContDiff ℝ 1 u)
    (hP : WeakPHarmonicPair p (ball (0 : Space n) R) u (gradient u))
    (hpositive : ∀ x ∈ ball (0 : Space n) R, 0 < u x)
    {ν : Space n} (hν : ‖ν‖ = 1) (hzero : u (R • ν) = 0) :
    0 < ⟪gradient u (R • ν),-ν⟫_ℝ ∧ gradient u (R • ν) ≠ 0 := by
  let r : ℝ := R/2
  have hr : 0 < r := by dsimp [r];linarith
  have hrR : r < R := by dsimp [r];linarith
  have hnonempty : (sphere (0 : Space n) r).Nonempty := by
    refine ⟨r • ν,?_⟩
    simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr,hν,mul_one]
  obtain ⟨y,hy,hmin⟩ := (isCompact_sphere (0 : Space n) r).exists_isMinOn hnonempty
    hu.continuous.continuousOn
  have hyr : ‖y‖ = r := by simpa only [mem_sphere,dist_zero_right] using hy
  have hm : 0 < u y := hpositive y (by simpa only [mem_ball,dist_zero_right,hyr] using hrR)
  have hinner : ∀ x : Space n, ‖x‖ = r → u y ≤ u x := by
    intro x hx
    exact hmin (by simpa only [mem_sphere,dist_zero_right] using hx)
  have hclosure : closure (ball (0 : Space n) R) ⊆ {x | 0 ≤ u x} :=
    closure_minimal (fun x hx => (hpositive x hx).le)
      (isClosed_le continuous_const hu.continuous)
  have houter : ∀ x : Space n, ‖x‖ = R → 0 ≤ u x := by
    intro x hx
    apply hclosure
    rw [closure_ball (0 : Space n) hR.ne']
    simpa only [mem_closedBall,dist_zero_right] using hx.le
  have hAnn : WeakPHarmonicPair p (radialAnnulus n r R) u (gradient u) :=
    hP.mono (fun x hx => by simpa only [mem_ball,dist_zero_right] using hx.2)
      (isOpen_radialAnnulus n r R)
  exact C1_annular_hopf hn hp hr hrR hm hu hAnn hinner houter hν hzero

end BMCompactPDE
end
end
end V5SegmentAnnularHopf

/-! Combined audit of every counted public supporting theorem. -/
#print axioms BMCompact.normalizationScale_pos
#print axioms BMCompact.normalizationWeight_pos
#print axioms BMCompact.normalizationWeight_lt_one
#print axioms BMCompact.normalizationWeight_complement
#print axioms BMCompact.normalization_left_coefficient
#print axioms BMCompact.normalization_right_coefficient
#print axioms BMCompact.normalization_vector_identity
#print axioms BMCompact.normalization_set_identity
#print axioms BMCompact.min_ge_weighted_sub_abs
#print axioms BMCompact.mem_closedNeighborhood_iff
#print axioms BMCompact.closedNeighborhood_eq_add_closedBall
#print axioms BMCompact.isCompact_closedNeighborhood
#print axioms BMCompact.subset_closedNeighborhood
#print axioms BMCompact.closedNeighborhood_mono
#print axioms BMCompact.iInter_closedNeighborhood
#print axioms BMCompact.eventually_closedNeighborhood_subset_open
#print axioms BMCompact.weighted_closedBall
#print axioms BMCompact.weighted_closedNeighborhood
#print axioms BMCompact.affine_closedNeighborhood
#print axioms BMCompact.geometric_mass_lower_bound
#print axioms BMCompact.no_positive_geometric_density
#print axioms BMCompact.geometric_radius_rpow
#print axioms BMCompact.geometric_rpow_density_lower_bound
#print axioms BMCompact.no_positive_rpow_density
#print axioms BMCompact.cone_density_contradiction
#print axioms BMCompactPDE.pFlux_zero
#print axioms BMCompactPDE.pFlux_neg
#print axioms BMCompactPDE.pFlux_two
#print axioms BMCompactPDE.rpow_coefficient_mul
#print axioms BMCompactPDE.norm_pFlux
#print axioms BMCompactPDE.pFlux_inner_self
#print axioms BMCompactPDE.pFlux_smul
#print axioms BMCompactPDE.pFlux_nonneg_smul
#print axioms BMCompactPDE.pFlux_pairing_lower_bound
#print axioms BMCompactPDE.pFlux_strict_monotonicity
#print axioms BMCompactPDE.pFlux_monotonicity
#print axioms BMCompactPDE.pFlux_injective
#print axioms BMCompactPDE.pFlux_eq_zero_iff
#print axioms BMCompactPDE.pFlux_pairing_eq_zero_iff
#print axioms BMCompactPDE.norm_pFlux_dual_power
#print axioms BMCompactPDE.continuous_pFlux
#print axioms BMCompactPDE.hasFDerivAt_energy_norm
#print axioms BMCompactPDE.hasFDerivAt_norm_rpow_nonzero
#print axioms BMCompactPDE.hasGradientAt_energy_norm
#print axioms BMCompactPDE.gradient_energy_norm
#print axioms BMCompactPDE.fundamentalPotential_zero_of_supercritical
#print axioms BMCompactPDE.normalizedRadialGradient_ne_zero
#print axioms BMCompactPDE.pFlux_normalizedRadialGradient
#print axioms BMCompactPDE.hasGradientAt_scalar_norm_rpow
#print axioms BMCompactPDE.hasGradientAt_radialPowerPotential
#print axioms BMCompactPDE.hasGradientAt_log_norm
#print axioms BMCompactPDE.hasGradientAt_criticalRadialPotential
#print axioms BMCompactPDE.hasGradientAt_fundamentalPotential
#print axioms BMCompactPDE.pFlux_gradient_fundamentalPotential
#print axioms BMCompactPDE.hasFDerivAt_norm_rpow_smul
#print axioms BMCompactPDE.classicalDivergence_norm_rpow_smul
#print axioms BMCompactPDE.classicalDivergence_const_smul
#print axioms BMCompactPDE.classicalDivergence_radialSourceFlux
#print axioms BMCompactPDE.classicalDivergence_pFlux_gradient_fundamentalPotential
#print axioms BMCompactPDE.contDiffAt_fundamentalPotential
#print axioms BMCompactPDE.contDiffOn_fundamentalPotential
#print axioms BMCompactPDE.contDiffAt_normalizedRadialGradient
#print axioms BMCompactPDE.classicalDivergence_eq_sum_fderiv_coordinates
#print axioms BMCompactPDE.classicalDivergence_eq_sum_gradient_coordinates
#print axioms BMCompactCapacityV2.admissible_of_subset
#print axioms BMCompactCapacityV2.relativeCapacity_mono
#print axioms BMCompactCapacityV2.variationalCapacity_mono
#print axioms BMCompactCapacityV2.relativeCapacity_le_energy
#print axioms BMCompactCapacityV2.gradient_hasCompactSupport
#print axioms BMCompactCapacityV2.continuous_gradient_of_contDiff
#print axioms BMCompactCapacityV2.smooth_compactSupport_memLp
#print axioms BMCompactCapacityV2.gradient_smooth_compactSupport_memLp
#print axioms BMCompactCapacityV2.gradient_const_mul
#print axioms BMCompactCapacityV2.pEnergy_const_mul
#print axioms BMCompactCapacityV2.pEnergy_ne_top_of_smooth_compactSupport
#print axioms BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
#print axioms BMCompactCapacityV2.pEnergy_eq_univ_of_tsupport_subset
#print axioms BMCompactCapacityV2.relativeCapacity_mono_domain
#print axioms BMCompactCapacityV2.relativeCapacity_empty
#print axioms BMCompactCapacityV2.variationalCapacity_empty
#print axioms BMCompactCapacityV2.tsupport_finset_sum_subset
#print axioms BMCompactCapacityV2.exists_admissible_of_isCompact
#print axioms BMCompactCapacityV2.exists_open_admissible_const_mul
#print axioms BMCompactCapacityV2.exists_open_capacity_le_scaled_energy
#print axioms BMCompactCapacityV2.relativeCapacity_ne_top_of_isCompact
#print axioms BMCompactCapacityV2.variationalCapacity_ne_top_of_isCompact
#print axioms BMCompactCapacityV2.le_of_forall_scaled_energy
#print axioms BMCompactCapacityV2.relativeCapacity_le_openEnlargementInf
#print axioms BMCompactCapacityV2.relativeCapacity_eq_openEnlargementInf
#print axioms BMCompactCapacityV2.monotone_relativeCapacity_cthickening
#print axioms BMCompactCapacityV2.relativeCapacity_eq_iInf_cthickening
#print axioms BMCompactCapacityV2.tendsto_relativeCapacity_cthickening
#print axioms BMCompactCapacityV2.tendsto_variationalCapacity_cthickening
#print axioms BMCompactPDE.smoothTest_zero
#print axioms BMCompactPDE.hasWeakGradientOn_zero
#print axioms BMCompactPDE.HasWeakGradientOn.add
#print axioms BMCompactPDE.HasWeakGradientOn.smul
#print axioms BMCompactPDE.sobolevPair_zero
#print axioms BMCompactPDE.SobolevPair.add
#print axioms BMCompactPDE.SobolevPair.smul
#print axioms BMCompactPDE.LocallySobolevPair.mono
#print axioms BMCompactPDE.zeroBoundarySobolevPair_zero
#print axioms BMCompactPDE.weakPHarmonicPair_zero
#print axioms BMCompactPDE.isWeakPHarmonic_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.mono
#print axioms BMCompactPDE.IsWeakPHarmonic.mono
#print axioms BMCompactPDE.WeakPHarmonicPair.supersolution
#print axioms BMCompactPDE.WeakPHarmonicPair.subsolution
#print axioms BMCompactPDE.HasWeakGradientOn.congr
#print axioms BMCompactPDE.SobolevPair.congr
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.congr
#print axioms BMCompactPDE.WeakPHarmonicPair.smul
#print axioms BMCompactPDE.IsWeakPHarmonic.smul
#print axioms BMCompactPDE.gradient_coordinate_eq_fderiv
#print axioms BMCompactPDE.hasWeakGradientOn_of_contDiff
#print axioms BMCompactPDE.SmoothTest.sobolevPair
#print axioms BMCompactPDE.SmoothTest.zeroBoundarySobolevPair
#print axioms BMCompactPDE.exists_nonzero_zeroBoundarySobolevPair
#print axioms BMCompactPDE.sobolevPair_const
#print axioms BMCompactPDE.weakPHarmonicPair_const
#print axioms BMCompactPDE.isWeakPHarmonic_const
#print axioms BMCompactPDE.hasWeakGradientOn_of_contDiffOn
#print axioms BMCompactPDE.HasWeakGradientOn.ae_unique
#print axioms BMCompactPDE.SobolevPair.gradient_ae_unique
#print axioms BMCompactPDE.WeakPHarmonicPair.gradient_ae_eq_of_zeroBoundaryDifference
#print axioms BMCompactPDE.holderConjugate_p_dual
#print axioms BMCompactPDE.memLp_pFlux
#print axioms BMCompactPDE.inner_integrable_of_memLp
#print axioms BMCompactPDE.zeroBoundary_integral_eq_zero_of_smoothTests
#print axioms BMCompactPDE.weakPHarmonicPair_of_smooth_test_equation
#print axioms BMCompactPDE.integral_inner_gradient_eq_neg_divergence
#print axioms BMCompactPDE.integral_inner_gradient_eq_zero_of_divergence_eq_zero
#print axioms BMCompactPDE.weakPHarmonicPair_of_divergence_eq_zero
#print axioms BMCompactPDE.weakPHarmonicPair_of_classicalDivergence_eq_zero
#print axioms BMCompactPDE.min_comparison_iInf
#print axioms BMCompactPDE.max_comparison_iSup
#print axioms BMCompactPDE.memLp_on_bounded_of_continuousOn_closure
#print axioms BMCompactPDE.continuousOn_gradient_of_contDiffOn
#print axioms BMCompactPDE.sobolevPair_of_contDiffOn
#print axioms BMCompactPDE.locallySobolevPair_of_contDiffOn
#print axioms BMCompactPDE.locallySobolevPair_fundamentalPotential
#print axioms BMCompactPDE.LocallySobolevPair.add_const
#print axioms BMCompactPDE.WeakPHarmonicPair.add_const
#print axioms BMCompactPDE.IsWeakPHarmonic.add_const
#print axioms BMCompactPDE.WeakPHarmonicPair.sub_const
#print axioms BMCompactPDE.IsWeakPHarmonic.sub_const
#print axioms BMCompactPDE.LocallySobolevPair.congr_fun
#print axioms BMCompactPDE.WeakPHarmonicPair.congr_fun
#print axioms BMCompactPDE.IsWeakPHarmonic.congr_on
#print axioms BMCompactPDE.contDiffAt_radialSourceFlux
#print axioms BMCompactPDE.contDiffOn_radialSourceFlux
#print axioms BMCompactPDE.contDiffOn_pFlux_gradient_fundamentalPotential
#print axioms BMCompactPDE.weakPHarmonicPair_fundamentalPotential
#print axioms BMCompactPDE.isWeakPHarmonic_fundamentalPotential
#print axioms BMCompactPDE.continuous_fundamentalPotential_supercritical
#print axioms BMCompactPDE.isExteriorGreen_singleton_fundamentalPotential
#print axioms BMCompactPDE.hasGreenAsymptotic_fundamentalPotential
#print axioms BMCompactPDE.greenCapacityOfConstant_zero_supercritical
#print axioms BMCompactPDE.fundamentalPotential_norm
#print axioms BMCompactPDE.ballGreen_eq_zero_of_norm_le
#print axioms BMCompactPDE.ballGreen_eq_profile_sub_of_le_norm
#print axioms BMCompactPDE.continuous_ballGreen
#print axioms BMCompactPDE.ballGreen_zero_on_closedBall
#print axioms BMCompactPDE.eventually_ballGreen_remainder_eq
#print axioms BMCompactPDE.ballGreen_hasBoundedGreenRemainder
#print axioms BMCompactPDE.ballGreen_hasGreenAsymptotic
#print axioms BMCompactPDE.ballGreen_isWeakPHarmonic
#print axioms BMCompactPDE.ballGreen_isExteriorGreen
#print axioms BMCompactPDE.exists_ballGreen_with_asymptotic
#print axioms BMCompactPDE.ballGreen_capacity_recipe_critical
#print axioms BMCompactPDE.ballGreen_capacity_recipe_supercritical
#print axioms BMCompactPDE.strictMonoOn_fundamentalRadialValue
#print axioms BMCompactPDE.fundamentalRadialValue_mono_positive
#print axioms BMCompactPDE.ballGreen_nonneg
#print axioms BMCompactPDE.ballGreen_pos_of_lt_norm
#print axioms BMCompactPDE.ballGreen_eq_zero_iff_norm_le
#print axioms BMCompactPDE.rpow_tail_lipschitz
#print axioms BMCompactPDE.abs_norm_translate_sub_norm_le
#print axioms BMCompactPDE.tendsto_norm_rpow_translate_sub
#print axioms BMCompactPDE.tendsto_log_norm_translate_sub
#print axioms BMCompactPDE.tendsto_fundamentalPotential_translate_sub
#print axioms BMCompactPDE.fundamentalPotential_dilate_critical
#print axioms BMCompactPDE.fundamentalPotential_dilate_supercritical
#print axioms BMCompactPDE.hasGradientAt_fundamentalPotential_sub
#print axioms BMCompactPDE.pFlux_gradient_fundamentalPotential_sub
#print axioms BMCompactPDE.contDiffOn_fundamentalPotential_sub
#print axioms BMCompactPDE.contDiffOn_pFlux_gradient_fundamentalPotential_sub
#print axioms BMCompactPDE.classicalDivergence_comp_sub_const
#print axioms BMCompactPDE.classicalDivergence_pFlux_gradient_fundamentalPotential_sub
#print axioms BMCompactPDE.weakPHarmonicPair_fundamentalPotential_sub
#print axioms BMCompactPDE.isWeakPHarmonic_fundamentalPotential_sub
#print axioms BMCompactPDE.translatedBallGreen_isWeakPHarmonic
#print axioms BMCompactPDE.HasGreenAsymptotic.boundedRemainder
#print axioms BMCompactPDE.HasGreenAsymptotic.unique
#print axioms BMCompactPDE.HasGreenAsymptotic.unique_of_dimension
#print axioms BMCompactPDE.HasBoundedGreenRemainder.congr_eventually
#print axioms BMCompactPDE.HasGreenAsymptotic.congr_eventually
#print axioms BMCompactPDE.translatedBallGreen_hasGreenAsymptotic
#print axioms BMCompactPDE.translatedBallGreen_isExteriorGreen
#print axioms BMCompactPDE.exists_translatedBallGreen_with_asymptotic
#print axioms BMCompactPDE.tendsto_eLpNorm_one_of_tendsto_eLpNorm_ofReal
#print axioms BMCompactPDE.exists_L1_poincare_constant
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.ae_eq_zero_of_gradient_ae_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.ae_eq_of_zeroBoundaryDifference
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.eqOn_zero_of_gradient_ae_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.eqOn_of_zeroBoundaryDifference
#print axioms BMCompactPDE.WeakPHarmonicPair.integral_smooth_test_eq_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.integral_zeroBoundary_eq_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.gradient_ae_eq_of_global_zeroBoundaryDifference
#print axioms BMCompactPDE.WeakPHarmonicPair.ae_eq_of_global_zeroBoundaryDifference
#print axioms BMCompactPDE.WeakPHarmonicPair.eqOn_of_global_zeroBoundaryDifference
#print axioms BMCompactPDE.WeakPHarmonicPair.positivePart_gradient_ae_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.ae_le_of_zeroBoundary_positivePart
#print axioms BMCompactPDE.WeakPHarmonicPair.leOn_of_zeroBoundary_positivePart
#print axioms BMCompactCapacityV2.subcriticalBM_of_neighborhood_BM
#print axioms BMCompactCapacityV2.contDiff_dilateTest
#print axioms BMCompactCapacityV2.hasCompactSupport_dilateTest
#print axioms BMCompactCapacityV2.contDiff_translateTest
#print axioms BMCompactCapacityV2.hasCompactSupport_translateTest
#print axioms BMCompactCapacityV2.gradient_comp_const_smul
#print axioms BMCompactCapacityV2.gradient_translateTest
#print axioms BMCompactCapacityV2.integrable_gradient_energy
#print axioms BMCompactCapacityV2.pEnergy_univ_eq_ofReal_integral
#print axioms BMCompactCapacityV2.pEnergy_dilateTest
#print axioms BMCompactCapacityV2.pEnergy_translateTest
#print axioms BMCompactCapacityV2.Admissible.dilateTest_univ
#print axioms BMCompactCapacityV2.Admissible.translateTest_univ
#print axioms BMCompactCapacityV2.variationalCapacity_dilate_le
#print axioms BMCompactCapacityV2.variationalCapacity_dilate
#print axioms BMCompactCapacityV2.variationalCapacity_translate_le
#print axioms BMCompactCapacityV2.variationalCapacity_translate
#print axioms BMCompactCapacityV2.variationalCapacity_affine
#print axioms BMCompactCapacityV2.Admissible.dilateTest
#print axioms BMCompactCapacityV2.Admissible.translateTest
#print axioms BMCompactCapacityV2.relativeCapacity_dilate_le
#print axioms BMCompactCapacityV2.relativeCapacity_dilate
#print axioms BMCompactCapacityV2.relativeCapacity_translate_le
#print axioms BMCompactCapacityV2.relativeCapacity_translate
#print axioms BMCompactCapacityV2.relativeCapacity_affine
#print axioms BMCompactCapacityV2.variationalCapacity_root_dilate
#print axioms BMCompactCapacityV2.subcriticalCapacityRoot_dilate
#print axioms BMCompactCapacityV2.subcriticalCapacityRoot_translate
#print axioms BMCompactCapacityV2.subcriticalCapacityRoot_nonneg
#print axioms BMCompactCapacityV2.normalization_pointwise_set_identity
#print axioms BMCompactCapacityV2.subcritical_BM_of_min_comparison
#print axioms BMCompactCapacityV2.ofReal_subcriticalCapacityRoot
#print axioms BMCompactCapacityV2.subcriticalCapacityRoot_mono
#print axioms BMCompactCapacityV2.weighted_capacityRoot_ge_left
#print axioms BMCompactCapacityV2.subcritical_BM_all_cases_of_min_comparison
#print axioms BMCompactCapacityV2.subcritical_ENNReal_BM_of_min_comparison
#print axioms BMCompactEnvelope.solved_blend
#print axioms BMCompactEnvelope.pairValue_blend
#print axioms BMCompactEnvelope.pairValue_diagonal
#print axioms BMCompactEnvelope.fibreValues_eq_range
#print axioms BMCompactEnvelope.continuous_pairValue
#print axioms BMCompactEnvelope.sSup_range_of_global_max
#print axioms BMCompactEnvelope.sSup_image_of_max
#print axioms BMCompactEnvelope.exists_global_max_pairValue
#print axioms BMCompactEnvelope.supConvolution_eq_compact_sup
#print axioms BMCompactEnvelope.exists_optimalPair_at_level
#print axioms BMCompactEnvelope.continuousAt_supConvolution_at_level
#print axioms BMCompactEnvelope.isCompact_superlevel_of_tendsto_zero
#print axioms BMCompactEnvelope.isCompact_superlevel_of_tendsto_atBot
#print axioms BMCompactEnvelope.exists_optimalPair_subcritical
#print axioms BMCompactEnvelope.continuous_supConvolution_subcritical
#print axioms BMCompactEnvelope.exists_optimalPair_atBot
#print axioms BMCompactEnvelope.continuous_supConvolution_atBot
#print axioms BMCompactEnvelope.fibreValues_nonempty
#print axioms BMCompactEnvelope.bddAbove_fibreValues_of_bound
#print axioms BMCompactEnvelope.min_le_supConvolution_of_decomposition
#print axioms BMCompactEnvelope.supConvolution_bounds
#print axioms BMCompactEnvelope.supConvolution_superlevel_eq_of_attained
#print axioms BMCompactEnvelope.supConvolution_top_level_eq_of_attained
#print axioms BMCompactEnvelope.supConvolution_superlevel_eq_subcritical
#print axioms BMCompactEnvelope.tendsto_supConvolution_zero
#print axioms BMCompactEnvelope.tendsto_supConvolution_atBot
#print axioms BMCompactEnvelope.norm_le_one_of_blend
#print axioms BMCompactEnvelope.supConvolution_le_radial_majorant
#print axioms BMCompactEnvelope.supConvolution_relative_radial_bound
#print axioms BMCompactEnvelope.tendsto_supConvolution_sub_smul_atBot
#print axioms BMCompactPDE.tendsto_fundamentalPotential_atTop
#print axioms BMCompactPDE.tendsto_negativeGreenEnvelope_add_atBot
#print axioms BMCompactAnalytic.touching_linear_equal_levels
#print axioms BMCompactAnalytic.touching_linear_positive_proportional
#print axioms BMCompactAnalytic.min_le_derivative_of_local_min_comparison
#print axioms BMCompactAnalytic.touching_first_variation
#print axioms BMCompactAnalytic.touching_fderiv_positive_proportional
#print axioms BMCompactAnalytic.touching_gradient_positive_proportional
#print axioms BMCompactAnalytic.unit_normal_of_positive_proportional
#print axioms BMCompactAnalytic.local_touching_gradient_harmonic_relation
#print axioms BMCompactAnalytic.contDiffAt_two_second_quotient
#print axioms BMCompactAnalytic.min_le_second_derivative_of_local_min_comparison
#print axioms BMCompactAnalytic.quadraticCurve_zero
#print axioms BMCompactAnalytic.quadraticCurve_hasDerivAt
#print axioms BMCompactAnalytic.quadraticCurve_contDiffAt
#print axioms BMCompactAnalytic.quadraticCurve_comp_deriv
#print axioms BMCompactAnalytic.quadraticCurve_comp_second_deriv
#print axioms BMCompactAnalytic.touching_hessian_of_proportional
#print axioms BMCompactAnalytic.local_touching_hessian_cubic_weights
#print axioms BMCompactAnalytic.supConvolution_local_touching
#print axioms BMCompactAnalytic.local_touching_gradient_and_hessian
#print axioms BMCompactAnalytic.supConvolution_upper_test_gradient_and_hessian
#print axioms BMCompactAnalytic.actualLaplacian_eq_sum
#print axioms BMCompactAnalytic.exists_orthonormalBasis_containing
#print axioms BMCompactAnalytic.normalizedPLaplacian_eq_aligned
#print axioms BMCompactAnalytic.normalizedPLaplacian_eq_zero_of_classical_eq_zero
#print axioms BMCompactAnalytic.elliptic_weighted_sum
#print axioms BMCompactAnalytic.aligned_normalizedPLaplacian_comparison
#print axioms BMCompactAnalytic.local_touching_normalizedPLaplacian_nonneg
#print axioms BMCompactAnalytic.actualLaplacian_euclidean_eq_sum
#print axioms BMCompactPDE.tendsto_eLpNorm_zero_of_dominated
#print axioms BMCompactPDE.deriv_smoothTransition_of_nonpos
#print axioms BMCompactPDE.deriv_smoothTransition_of_one_le
#print axioms BMCompactPDE.smoothPositivePart_contDiff
#print axioms BMCompactPDE.smoothPositivePart_hasDerivAt
#print axioms BMCompactPDE.smoothPositivePart_eq_zero_of_nonpos
#print axioms BMCompactPDE.positivePartSlope_eq_zero_of_nonpos
#print axioms BMCompactPDE.smoothPositivePart_eq_self_of_one_le
#print axioms BMCompactPDE.positivePartSlope_eq_one_of_one_le
#print axioms BMCompactPDE.smoothPositivePart_norm_le
#print axioms BMCompactPDE.positivePartSlope_uniform_bound
#print axioms BMCompactPDE.smoothPositivePart_eventually_eq
#print axioms BMCompactPDE.positivePartSlope_eventually_eq
#print axioms BMCompactPDE.gradient_smoothPositivePart_comp
#print axioms BMCompactPDE.positivePartGradient_aestronglyMeasurable
#print axioms BMCompactPDE.positivePartGradient_norm_le
#print axioms BMCompactPDE.hasWeakGradientOn_positivePart_of_contDiff
#print axioms BMCompactPDE.positivePart_zeroBoundarySobolevPair_of_contDiff
#print axioms BMCompactPDE.SmoothTest.positivePart_zeroBoundarySobolevPair
#print axioms BMCompactPDE.gradient_fun_sub
#print axioms BMCompactPDE.WeakPHarmonicPair.leOn_of_contDiff_compact_positivePart_finiteEnergy
#print axioms BMCompactPDE.WeakPHarmonicPair.leOn_of_contDiff_compact_positivePart
#print axioms BMCompactPDE.positivePart_sub_zeroBoundary_of_boundary_nonpos
#print axioms BMCompactPDE.WeakPHarmonicPair.leOn_of_contDiff_boundary_order
#print axioms BMCompactCapacityV2.relativeCapacity_le_innerCondenserCapacity
#print axioms BMCompactCapacityV2.innerCondenserCapacity_le_relativeCapacity
#print axioms BMCompactCapacityV2.innerCondenserCapacity_mono
#print axioms BMCompactCapacityV2.innerCondenserCapacity_mono_domain
#print axioms BMCompactCapacityV2.outerCondenserCapacity_le_inner
#print axioms BMCompactCapacityV2.relativeCapacity_le_outerCondenserCapacity_of_isCompact
#print axioms BMCompactCapacityV2.outerCondenserCapacity_le_openEnlargementInf
#print axioms BMCompactCapacityV2.outerCondenserCapacity_eq_relativeCapacity_of_isCompact
#print axioms BMCompactCapacityV2.outerCondenserCapacity_mono
#print axioms BMCompactCapacityV2.outerCondenserCapacity_mono_domain
#print axioms BMCompactCapacityV2.outerCondenserCapacity_eq_inner_of_isOpen
#print axioms BMCompactCapacityV2.innerCondenserCapacity_image
#print axioms BMCompactCapacityV2.outerCondenserCapacity_image
#print axioms BMCompactCapacityV2.condenserAffineHomeomorph_image
#print axioms BMCompactCapacityV2.innerCondenserCapacity_affine
#print axioms BMCompactCapacityV2.outerCondenserCapacity_affine
#print axioms BMCompactPDE.hasFDerivAt_pFlux
#print axioms BMCompactPDE.contDiffAt_pFlux
#print axioms BMCompactPDE.hasFDerivAt_pFlux_comp
#print axioms BMCompactPDE.classicalDivergence_pFlux_comp
#print axioms BMCompactPDE.hasFDerivAt_gradient_of_contDiffAt_two
#print axioms BMCompactPDE.fderiv_gradient_eq_actualHessianEnd
#print axioms BMCompactPDE.inner_fderiv_gradient_eq_actualHessian
#print axioms BMCompactPDE.classicalDivergence_pFlux_gradient_eq_classicalPLaplacian
#print axioms BMCompactPDE.hasWeakGradientOn_of_contDiffOn_one
#print axioms BMCompactPDE.continuousOn_gradient_of_contDiffOn_one
#print axioms BMCompactPDE.sobolevPair_of_contDiffOn_one
#print axioms BMCompactPDE.locallySobolevPair_of_contDiffOn_one
#print axioms BMCompactPDE.integral_inner_gradient_eq_neg_divergence_one
#print axioms BMCompactPDE.integral_inner_gradient_eq_zero_of_divergence_eq_zero_one
#print axioms BMCompactPDE.weakPHarmonicPair_of_divergence_eq_zero_one
#print axioms BMCompactPDE.contDiffOn_gradient_of_contDiffOn_two
#print axioms BMCompactPDE.contDiffOn_pFlux_gradient_of_contDiffOn_two
#print axioms BMCompactPDE.continuousOn_coordinateDivergence_of_contDiffOn_one
#print axioms BMCompactPDE.eqOn_zero_of_continuousOn_integral_smoothTests_eq_zero
#print axioms BMCompactPDE.weakPHarmonicPair_of_classicalPLaplacian_eq_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.classicalPLaplacian_eq_zero
#print axioms BMCompactPDE.weakPHarmonicPair_iff_classicalPLaplacian_eq_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.classicalPLaplacian_eq_zero_at
#print axioms BMCompactPDE.WeakPHarmonicPair.with_classical_gradient
#print axioms BMCompactPDE.IsWeakPHarmonic.classicalPLaplacian_eq_zero_at
#print axioms BMCompactAnalytic.fderiv_eq_of_local_upper_contact
#print axioms BMCompactAnalytic.gradient_eq_of_local_upper_contact
#print axioms BMCompactAnalytic.hessian_le_of_local_upper_contact
#print axioms BMCompactAnalytic.normalizedPLaplacian_le_of_local_upper_contact
#print axioms BMCompactAnalytic.gradient_add_const
#print axioms BMCompactAnalytic.actualHessian_add_const
#print axioms BMCompactAnalytic.actualLaplacian_add_const
#print axioms BMCompactAnalytic.normalizedPLaplacian_add_const
#print axioms BMCompactAnalytic.IsViscosityPSubsolution.mono
#print axioms BMCompactAnalytic.IsViscosityPSubsolution.manuscript
#print axioms BMCompactAnalytic.IsViscosityPSubsolution.add_const
#print axioms BMCompactAnalytic.viscosityPSubsolution_of_classical_normalized
#print axioms BMCompactAnalytic.viscosityPSubsolution_of_classical_eq_zero
#print axioms BMCompactAnalytic.manuscriptViscosityPSubsolution_of_classical_eq_zero
#print axioms BMCompactAnalytic.IsViscosityPSubsolution.leOn_of_strict_classical_supersolution
#print axioms BMCompactPDE.memLp_coordinate
#print axioms BMCompactPDE.tendsto_eLpNorm_coordinate_sub
#print axioms BMCompactPDE.tendsto_integral_mul_of_eLpNorm
#print axioms BMCompactPDE.hasWeakGradientOn_of_eLpNorm_limits
#print axioms BMCompactPDE.sobolevPair_of_eLpNorm_limits
#print axioms BMCompactPDE.eLpNorm_sub_le_via
#print axioms BMCompactPDE.zeroBoundarySobolevPair_of_eLpNorm_limits
#print axioms BMCompactPDE.continuous_positivePartSlope
#print axioms BMCompactPDE.smoothPositivePart_norm_sub_le
#print axioms BMCompactPDE.tendsto_eLpNorm_bounded_smul
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.smoothPositivePart
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.positivePart
#print axioms BMCompactPDE.contDiff_normalizedMollify
#print axioms BMCompactPDE.hasCompactSupport_normalizedMollify
#print axioms BMCompactPDE.tsupport_normalizedMollify_subset
#print axioms BMCompactPDE.norm_normalizedMollify_le
#print axioms BMCompactPDE.tendsto_normalizedMollify
#print axioms BMCompactPDE.fderiv_normalizedMollify
#print axioms BMCompactPDE.tendsto_fderiv_normalizedMollify
#print axioms BMCompactPDE.tendsto_eLpNorm_zero_of_compact_uniform_bound
#print axioms BMCompactPDE.tendsto_eLpNorm_mollify_sub
#print axioms BMCompactPDE.zeroBoundarySobolevPair_of_contDiff_one_compactSupport
#print axioms BMCompactPDE.positivePart_sub_zeroBoundary_of_C1_boundary_nonpos
#print axioms BMCompactPDE.WeakPHarmonicPair.leOn_of_C1_boundary_order
#print axioms BMCompactPDE.hasGradientAt_radialPowerPotential_all_p
#print axioms BMCompactPDE.hasGradientAt_fundamentalPotential_all_p
#print axioms BMCompactPDE.pFlux_gradient_fundamentalPotential_all_p
#print axioms BMCompactPDE.contDiffOn_pFlux_gradient_fundamentalPotential_all_p
#print axioms BMCompactPDE.classicalDivergence_pFlux_gradient_fundamentalPotential_all_p
#print axioms BMCompactPDE.weakPHarmonicPair_fundamentalPotential_all_p
#print axioms BMCompactPDE.strictMonoOn_fundamentalRadialValue_all_p
#print axioms BMCompactAnalytic.upperTest_isLocalMin_of_left_strict
#print axioms BMCompactAnalytic.upperTest_isLocalMin_of_right_strict
#print axioms BMCompactAnalytic.touching_fderiv_eq_zero_of_left_zero
#print axioms BMCompactAnalytic.touching_fderiv_eq_zero_of_right_zero
#print axioms BMCompactAnalytic.gradient_eq_zero_of_isLocalMin
#print axioms BMCompactAnalytic.fderiv_eq_zero_of_gradient_eq_zero
#print axioms BMCompactAnalytic.supConvolution_optimizer_balanced
#print axioms BMCompactAnalytic.supConvolution_optimizer_balanced_noncritical
#print axioms BMCompactAnalytic.supConvolution_optimizer_nondegenerate_below_level
#print axioms BMCompactAnalytic.viscosity_supConvolution_of_attainment
#print axioms BMCompactAnalytic.viscosity_supConvolution_subcritical
#print axioms BMCompactAnalytic.viscosity_supConvolution_atBot
#print axioms BMCompactPDE.WeakPHarmonicPair.classicalPLaplacian_eq_zero_of_contDiffAt_two
#print axioms BMCompactPDE.IsWeakPHarmonic.classicalPLaplacian_eq_zero_of_contDiffAt_two
#print axioms BMCompactPDE.IsWeakPHarmonic.viscosity_of_C1_noncritical_C2
#print axioms BMCompactPDE.IsWeakPHarmonic.manuscriptViscosity_of_C1_noncritical_C2
#print axioms BMCompactAnalytic.weak_viscosity_supConvolution_of_attainment
#print axioms BMCompactAnalytic.weak_viscosity_supConvolution_subcritical
#print axioms BMCompactAnalytic.weak_viscosity_supConvolution_atBot
#print axioms BMCompactPDE.annularBarrierDenominator_pos
#print axioms BMCompactPDE.annularRadialBarrier_zero_outer
#print axioms BMCompactPDE.annularRadialBarrier_one_inner
#print axioms BMCompactPDE.annularRadialBarrier_bounds
#print axioms BMCompactPDE.annularRadialBarrier_pos
#print axioms BMCompactPDE.contDiff_flattenedRadialPrimitive
#print axioms BMCompactPDE.flattenedRadialPrimitive_eq
#print axioms BMCompactPDE.flattenedRadialPrimitive_eventuallyEq
#print axioms BMCompactPDE.WeakPHarmonicPair.congr_gradient_on
#print axioms BMCompactPDE.weakPHarmonicPair_flattenedRadialPrimitive
#print axioms BMCompactPDE.contDiff_annularSmoothBarrier
#print axioms BMCompactPDE.annularSmoothBarrier_eq
#print axioms BMCompactPDE.weakPHarmonicPair_annularSmoothBarrier
#print axioms BMCompactPDE.isOpen_radialAnnulus
#print axioms BMCompactPDE.isBounded_radialAnnulus
#print axioms BMCompactPDE.norm_of_mem_frontier_radialAnnulus
#print axioms BMCompactPDE.annularRadialBarrier_le_of_C1_weak_harmonic
#print axioms BMCompactPDE.derivative_le_of_eventually_le_right
#print axioms BMCompactPDE.inward_derivative_annularRadialBarrier
#print axioms BMCompactPDE.annular_inward_derivative_lower_bound
#print axioms BMCompactPDE.C1_annular_hopf
#print axioms BMCompactPDE.C1_ball_hopf
