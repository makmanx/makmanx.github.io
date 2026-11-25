import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
set_option autoImplicit false

namespace BMCompactPDE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual nonlinear flux used by the p-Laplace equation. -/
def pFlux (p : ℝ) (v : E) : E := ‖v‖ ^ (p - 2) • v

@[simp] theorem pFlux_zero (p : ℝ) : pFlux p (0 : E) = 0 := by
  simp [pFlux]

@[simp] theorem pFlux_neg (p : ℝ) (v : E) : pFlux p (-v) = -pFlux p v := by
  simp [pFlux]

@[simp] theorem pFlux_two (v : E) : pFlux 2 v = v := by
  simp [pFlux]

end BMCompactPDE
