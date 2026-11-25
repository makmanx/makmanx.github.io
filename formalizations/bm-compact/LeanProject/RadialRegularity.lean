import FundamentalProfiles
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
set_option autoImplicit false
open scoped ContDiff

namespace BMCompactPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Here `∞` is the genuine smoothness order, rather than the analytic order `⊤`. -/
theorem contDiffAt_fundamentalPotential (n : ℕ) (σ p : ℝ) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fundamentalPotential n σ p : E → ℝ) x := by
  have hnrm : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  by_cases h : p = (n : ℝ)
  · have hf : (fundamentalPotential n σ p : E → ℝ) =
        criticalRadialPotential n σ := by
      funext y
      simp [fundamentalPotential, h]
    rw [hf]
    exact (contDiffAt_const.mul (hnrm.log hnorm)).add contDiffAt_const
  · have hf : (fundamentalPotential n σ p : E → ℝ) =
        radialPowerPotential n σ p := by
      funext y
      simp [fundamentalPotential, h]
    rw [hf]
    exact contDiffAt_const.mul (hnrm.rpow_const_of_ne hnorm)

theorem contDiffOn_fundamentalPotential (n : ℕ) (σ p : ℝ) :
    ContDiffOn ℝ ∞ (fundamentalPotential n σ p : E → ℝ) {x : E | x ≠ 0} := by
  intro x hx
  exact (contDiffAt_fundamentalPotential n σ p hx).contDiffWithinAt

theorem contDiffAt_normalizedRadialGradient (n : ℕ) (σ p : ℝ) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (normalizedRadialGradient n σ p : E → E) x := by
  have hnrm : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx
  exact (contDiffAt_const.mul (hnrm.rpow_const_of_ne
    (norm_ne_zero_iff.mpr hx))).smul contDiffAt_id

end BMCompactPDE

#print axioms BMCompactPDE.contDiffAt_fundamentalPotential
#print axioms BMCompactPDE.contDiffOn_fundamentalPotential
#print axioms BMCompactPDE.contDiffAt_normalizedRadialGradient
