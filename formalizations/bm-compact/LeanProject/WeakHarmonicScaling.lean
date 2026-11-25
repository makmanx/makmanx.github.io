import WeakPDE
import GreenFoundation

/-! Actual nonlinear weak p-Laplace invariance under arbitrary real scaling.
The proof scales the p-flux by its concrete scalar coefficient; it does not
assume linearity of the p-Laplacian. -/

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace BMCompactPDE

theorem WeakPHarmonicPair.smul {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (a : ℝ) :
    WeakPHarmonicPair p Ω (a • u) (a • g) := by
  refine ⟨hu.1, hu.2.1, fun D hD => (hu.2.2.1 D hD).smul a, ?_⟩
  intro D hD θ h hθ
  obtain ⟨hi, heq⟩ := hu.2.2.2 D hD θ h hθ
  have hscale : fluxPairing p (a • g) h =
      fun x => (|a| ^ (p - 2) * a) * fluxPairing p g h x := by
    funext x
    simp only [fluxPairing, Pi.smul_apply, pFlux_smul, real_inner_smul_left]
  rw [hscale]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, heq, mul_zero]

theorem IsWeakPHarmonic.smul {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hu : IsWeakPHarmonic p Ω u) (a : ℝ) :
    IsWeakPHarmonic p Ω (a • u) := by
  obtain ⟨g, hg⟩ := hu
  exact ⟨a • g, hg.smul a⟩

end BMCompactPDE

#print axioms BMCompactPDE.WeakPHarmonicPair.smul
#print axioms BMCompactPDE.IsWeakPHarmonic.smul
