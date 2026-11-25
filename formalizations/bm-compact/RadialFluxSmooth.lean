import RadialRegularity
import RadialDivergence

/-! The actual p-flux of the source's radial profile is genuinely C-infinity
away from its pole, as required by the classical-to-weak criterion. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff InnerProductSpace
namespace BMCompactPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiffAt_radialSourceFlux (n : ℕ) (σ : ℝ) {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (radialSourceFlux n σ : E → E) x := by
  have hnorm : ContDiffAt ℝ ∞ (fun y : E => ‖y‖) x := contDiffAt_norm ℝ hx
  exact (contDiffAt_const.mul (hnorm.rpow_const_of_ne
    (norm_ne_zero_iff.mpr hx))).smul contDiffAt_id

theorem contDiffOn_radialSourceFlux (n : ℕ) (σ : ℝ) :
    ContDiffOn ℝ ∞ (radialSourceFlux n σ : E → E) {x : E | x ≠ 0} := by
  intro x hx
  exact (contDiffAt_radialSourceFlux n σ hx).contDiffWithinAt

theorem contDiffOn_pFlux_gradient_fundamentalPotential [CompleteSpace E]
    (n : ℕ) {σ p : ℝ} (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) :
    ContDiffOn ℝ ∞
      (fun x : E => pFlux p (gradient (fundamentalPotential n σ p : E → ℝ) x))
      {x : E | x ≠ 0} := by
  apply (contDiffOn_radialSourceFlux (E := E) n σ).congr
  intro x hx
  exact pFlux_gradient_fundamentalPotential n hσ hn hpn hx

end BMCompactPDE
#print axioms BMCompactPDE.contDiffAt_radialSourceFlux
#print axioms BMCompactPDE.contDiffOn_radialSourceFlux
#print axioms BMCompactPDE.contDiffOn_pFlux_gradient_fundamentalPotential
