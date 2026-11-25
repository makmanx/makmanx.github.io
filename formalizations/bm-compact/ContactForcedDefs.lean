import BMCompactCriticalChecked

/-! Actual constant-source weak equations and inequalities in the existing
concrete distributional Sobolev graph. These are definitions, not existence
or regularity assertions. The source term is the ordinary Lebesgue integral
of the actual zero-boundary test representative. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

def WeakPSourcePair {n : ℕ} (p c : ℝ) (Ω : Set (Space n))
    (u : Space n → ℝ) (g : Space n → Space n) : Prop :=
  1 < p ∧ IsOpen Ω ∧ LocallySobolevPair p Ω u g ∧
    ∀ D : Set (Space n), LocalDomain D Ω →
      ∀ (θ : Space n → ℝ) (h : Space n → Space n),
        ZeroBoundarySobolevPair p D θ h →
          Integrable (fluxPairing p g h) (volume.restrict D) ∧
            (∫ x in D, fluxPairing p g h x) = c * ∫ x in D, θ x

def WeakPSourceSubsolutionPair {n : ℕ} (p c : ℝ) (Ω : Set (Space n))
    (u : Space n → ℝ) (g : Space n → Space n) : Prop :=
  1 < p ∧ IsOpen Ω ∧ LocallySobolevPair p Ω u g ∧
    ∀ D : Set (Space n), LocalDomain D Ω →
      ∀ (θ : Space n → ℝ) (h : Space n → Space n),
        ZeroBoundarySobolevPair p D θ h →
          (∀ᵐ x ∂(volume.restrict D), 0 ≤ θ x) →
            Integrable (fluxPairing p g h) (volume.restrict D) ∧
              (∫ x in D, fluxPairing p g h x) ≤ c * ∫ x in D, θ x

def WeakPSourceSupersolutionPair {n : ℕ} (p c : ℝ) (Ω : Set (Space n))
    (u : Space n → ℝ) (g : Space n → Space n) : Prop :=
  1 < p ∧ IsOpen Ω ∧ LocallySobolevPair p Ω u g ∧
    ∀ D : Set (Space n), LocalDomain D Ω →
      ∀ (θ : Space n → ℝ) (h : Space n → Space n),
        ZeroBoundarySobolevPair p D θ h →
          (∀ᵐ x ∂(volume.restrict D), 0 ≤ θ x) →
            Integrable (fluxPairing p g h) (volume.restrict D) ∧
              c * (∫ x in D, θ x) ≤ ∫ x in D, fluxPairing p g h x

end BMCompactPDE
