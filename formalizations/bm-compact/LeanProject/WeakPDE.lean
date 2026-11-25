import FluxDefs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Topology.Algebra.Support

/-!
Concrete weak-gradient, Sobolev-pair, and weak p-Laplace definitions.
Classical gradients occur only for smooth test functions and their smooth
approximants. The gradient field of an arbitrary Sobolev function is an
independent field constrained by distributional integration by parts.

The graph-closure definition of zero boundary values is explicit. Theorems
identifying this model with alternative Sobolev quotient-space constructions,
weak-gradient uniqueness, and the extension of the smooth-test equation by
density are separate obligations, not assumed results in this file.
-/

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace BMCompactPDE

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- A genuine globally smooth test function with compact support in a domain. -/
def SmoothTest {n : ℕ} (Ω : Set (Space n)) (φ : Space n → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- Distributional gradient on Ω, with integrability retained explicitly.
The equation is imposed in each standard Euclidean coordinate. -/
def HasWeakGradientOn {n : ℕ} (Ω : Set (Space n))
    (u : Space n → ℝ) (g : Space n → Space n) : Prop :=
  ∀ φ : Space n → ℝ, SmoothTest Ω φ → ∀ i : Fin n,
    Integrable (fun x => u x * (gradient φ x) i) (volume.restrict Ω) ∧
    Integrable (fun x => (g x) i * φ x) (volume.restrict Ω) ∧
      (∫ x in Ω, u x * (gradient φ x) i) =
        -(∫ x in Ω, (g x) i * φ x)

/-- A concrete W^{1,p} function together with its weak gradient (p>1). -/
def SobolevPair {n : ℕ} (p : ℝ) (Ω : Set (Space n))
    (u : Space n → ℝ) (g : Space n → Space n) : Prop :=
  1 < p ∧ MemLp u (ENNReal.ofReal p) (volume.restrict Ω) ∧
    MemLp g (ENNReal.ofReal p) (volume.restrict Ω) ∧ HasWeakGradientOn Ω u g

/-- The exact bounded-open local domains used in the manuscript's weak equation. -/
def LocalDomain {n : ℕ} (D Ω : Set (Space n)) : Prop :=
  IsOpen D ∧ Bornology.IsBounded D ∧ closure D ⊆ Ω

def LocallySobolevPair {n : ℕ} (p : ℝ) (Ω : Set (Space n))
    (u : Space n → ℝ) (g : Space n → Space n) : Prop :=
  ∀ D : Set (Space n), LocalDomain D Ω → SobolevPair p D u g

/-- W^{1,p}_0 in the concrete weak-gradient graph: smooth compact-support
approximants converge in both L^p components. -/
def ZeroBoundarySobolevPair {n : ℕ} (p : ℝ) (D : Set (Space n))
    (u : Space n → ℝ) (g : Space n → Space n) : Prop :=
  SobolevPair p D u g ∧
    ∃ φ : ℕ → Space n → ℝ,
      (∀ j, SmoothTest D (φ j)) ∧
      Tendsto (fun j => eLpNorm (φ j - u) (ENNReal.ofReal p) (volume.restrict D))
        atTop (𝓝 0) ∧
      Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x - g x)
        (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0)

def fluxPairing {n : ℕ} (p : ℝ) (g h : Space n → Space n) (x : Space n) : ℝ :=
  inner ℝ (pFlux p (g x)) (h x)

/-- The weak equation is tested against every zero-boundary Sobolev pair,
not merely against smooth tests. The weak gradient is never classical fderiv(u). -/
def WeakPHarmonicPair {n : ℕ} (p : ℝ) (Ω : Set (Space n))
    (u : Space n → ℝ) (g : Space n → Space n) : Prop :=
  1 < p ∧ IsOpen Ω ∧ LocallySobolevPair p Ω u g ∧
    ∀ D : Set (Space n), LocalDomain D Ω →
      ∀ (θ : Space n → ℝ) (h : Space n → Space n),
        ZeroBoundarySobolevPair p D θ h →
          Integrable (fluxPairing p g h) (volume.restrict D) ∧
            (∫ x in D, fluxPairing p g h x) = 0

def IsWeakPHarmonic {n : ℕ} (p : ℝ) (Ω : Set (Space n)) (u : Space n → ℝ) : Prop :=
  ∃ g : Space n → Space n, WeakPHarmonicPair p Ω u g

def WeakPSupersolutionPair {n : ℕ} (p : ℝ) (Ω : Set (Space n))
    (u : Space n → ℝ) (g : Space n → Space n) : Prop :=
  1 < p ∧ IsOpen Ω ∧ LocallySobolevPair p Ω u g ∧
    ∀ D : Set (Space n), LocalDomain D Ω →
      ∀ (θ : Space n → ℝ) (h : Space n → Space n),
        ZeroBoundarySobolevPair p D θ h →
          (∀ᵐ x ∂(volume.restrict D), 0 ≤ θ x) →
            Integrable (fluxPairing p g h) (volume.restrict D) ∧
              0 ≤ (∫ x in D, fluxPairing p g h x)

def WeakPSubsolutionPair {n : ℕ} (p : ℝ) (Ω : Set (Space n))
    (u : Space n → ℝ) (g : Space n → Space n) : Prop :=
  1 < p ∧ IsOpen Ω ∧ LocallySobolevPair p Ω u g ∧
    ∀ D : Set (Space n), LocalDomain D Ω →
      ∀ (θ : Space n → ℝ) (h : Space n → Space n),
        ZeroBoundarySobolevPair p D θ h →
          (∀ᵐ x ∂(volume.restrict D), 0 ≤ θ x) →
            Integrable (fluxPairing p g h) (volume.restrict D) ∧
              (∫ x in D, fluxPairing p g h x) ≤ 0

theorem smoothTest_zero {n : ℕ} (Ω : Set (Space n)) : SmoothTest Ω 0 := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · simp [HasCompactSupport]
  · simp

theorem hasWeakGradientOn_zero {n : ℕ} (Ω : Set (Space n)) :
    HasWeakGradientOn Ω 0 0 := by
  intro φ _ i
  simp

theorem HasWeakGradientOn.add {n : ℕ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : HasWeakGradientOn Ω u g) (hv : HasWeakGradientOn Ω v h) :
    HasWeakGradientOn Ω (u + v) (g + h) := by
  intro φ hφ i
  obtain ⟨hui, hgi, hEqU⟩ := hu φ hφ i
  obtain ⟨hvi, hhi, hEqV⟩ := hv φ hφ i
  refine ⟨?_, ?_, ?_⟩
  · convert hui.add hvi using 1 <;> first | rfl | (ext x; simp [add_mul])
  · convert hgi.add hhi using 1 <;> first | rfl | (ext x; simp [add_mul])
  · simp only [Pi.add_apply, PiLp.add_apply, add_mul]
    rw [integral_add hui hvi, integral_add hgi hhi, hEqU, hEqV, neg_add]

theorem HasWeakGradientOn.smul {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : HasWeakGradientOn Ω u g) (c : ℝ) :
    HasWeakGradientOn Ω (c • u) (c • g) := by
  intro φ hφ i
  obtain ⟨hui, hgi, hEq⟩ := hu φ hφ i
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using hui.const_mul c
  · simpa only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, mul_assoc] using hgi.const_mul c
  · simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, integral_const_mul, hEq, mul_neg]

theorem sobolevPair_zero {n : ℕ} {p : ℝ} (hp : 1 < p) (Ω : Set (Space n)) :
    SobolevPair p Ω 0 0 :=
  ⟨hp, MemLp.zero, MemLp.zero, hasWeakGradientOn_zero Ω⟩

theorem SobolevPair.add {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hv : SobolevPair p Ω v h) :
    SobolevPair p Ω (u + v) (g + h) :=
  ⟨hu.1, hu.2.1.add hv.2.1, hu.2.2.1.add hv.2.2.1,
    hu.2.2.2.add hv.2.2.2⟩

theorem SobolevPair.smul {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (c : ℝ) : SobolevPair p Ω (c • u) (c • g) :=
  ⟨hu.1, hu.2.1.const_smul c, hu.2.2.1.const_smul c, hu.2.2.2.smul c⟩

theorem LocallySobolevPair.mono {n : ℕ} {p : ℝ} {Ω U : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : LocallySobolevPair p Ω u g) (hU : U ⊆ Ω) :
    LocallySobolevPair p U u g := by
  intro D hD
  exact hu D ⟨hD.1, hD.2.1, hD.2.2.trans hU⟩

theorem zeroBoundarySobolevPair_zero {n : ℕ} {p : ℝ} (hp : 1 < p)
    (D : Set (Space n)) : ZeroBoundarySobolevPair p D 0 0 := by
  refine ⟨sobolevPair_zero hp D, ⟨fun _ => 0, fun _ => smoothTest_zero D, ?_, ?_⟩⟩
  · simpa [Pi.zero_def, gradient] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  · simpa [Pi.zero_def, gradient] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

theorem weakPHarmonicPair_zero {n : ℕ} {p : ℝ} (hp : 1 < p)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) : WeakPHarmonicPair p Ω 0 0 := by
  refine ⟨hp, hΩ, fun D _ => sobolevPair_zero hp D, ?_⟩
  intro D _ θ h _
  have hzero : fluxPairing p (0 : Space n → Space n) h = 0 := by
    funext x
    simp [fluxPairing]
  rw [hzero]
  simp

theorem isWeakPHarmonic_zero {n : ℕ} {p : ℝ} (hp : 1 < p)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) : IsWeakPHarmonic p Ω 0 :=
  ⟨0, weakPHarmonicPair_zero hp hΩ⟩

theorem WeakPHarmonicPair.mono {n : ℕ} {p : ℝ} {Ω U : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hU : U ⊆ Ω) (hUopen : IsOpen U) :
    WeakPHarmonicPair p U u g := by
  refine ⟨hu.1, hUopen, hu.2.2.1.mono hU, ?_⟩
  intro D hD θ h hθ
  exact hu.2.2.2 D ⟨hD.1, hD.2.1, hD.2.2.trans hU⟩ θ h hθ

theorem IsWeakPHarmonic.mono {n : ℕ} {p : ℝ} {Ω U : Set (Space n)}
    {u : Space n → ℝ} (hu : IsWeakPHarmonic p Ω u)
    (hU : U ⊆ Ω) (hUopen : IsOpen U) : IsWeakPHarmonic p U u := by
  obtain ⟨g, hg⟩ := hu
  exact ⟨g, hg.mono hU hUopen⟩

theorem WeakPHarmonicPair.supersolution {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n} (hu : WeakPHarmonicPair p Ω u g) :
    WeakPSupersolutionPair p Ω u g := by
  refine ⟨hu.1, hu.2.1, hu.2.2.1, ?_⟩
  intro D hD θ h hθ _
  obtain ⟨hi, heq⟩ := hu.2.2.2 D hD θ h hθ
  exact ⟨hi, heq.ge⟩

theorem WeakPHarmonicPair.subsolution {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n} (hu : WeakPHarmonicPair p Ω u g) :
    WeakPSubsolutionPair p Ω u g := by
  refine ⟨hu.1, hu.2.1, hu.2.2.1, ?_⟩
  intro D hD θ h hθ _
  obtain ⟨hi, heq⟩ := hu.2.2.2 D hD θ h hθ
  exact ⟨hi, heq.le⟩

end BMCompactPDE

#print axioms BMCompactPDE.HasWeakGradientOn.add
#print axioms BMCompactPDE.HasWeakGradientOn.smul
#print axioms BMCompactPDE.SobolevPair.add
#print axioms BMCompactPDE.SobolevPair.smul
#print axioms BMCompactPDE.zeroBoundarySobolevPair_zero
#print axioms BMCompactPDE.isWeakPHarmonic_zero
#print axioms BMCompactPDE.IsWeakPHarmonic.mono
#print axioms BMCompactPDE.WeakPHarmonicPair.supersolution
#print axioms BMCompactPDE.WeakPHarmonicPair.subsolution
