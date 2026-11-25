import RadialRegularity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Genuine global continuity of the supercritical radial profile, including
its prescribed value0 at the pole; no critical continuity claim is made. -/
noncomputable section
set_option autoImplicit false
namespace BMCompactPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuous_fundamentalPotential_supercritical (n : ℕ) (σ : ℝ) {p : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) < p) :
    Continuous (fundamentalPotential n σ p : E → ℝ) := by
  have hpne : p ≠ (n : ℝ) := ne_of_gt hpn
  have hq : 0 < (p - (n : ℝ)) / (p - 1) :=
    div_pos (sub_pos.mpr hpn) (sub_pos.mpr (hn.trans hpn))
  have heq : (fundamentalPotential n σ p : E → ℝ) =
      fun x : E => (((p - (n : ℝ)) / (p - 1))⁻¹ * σ ^ (-(p - 1)⁻¹)) *
        ‖x‖ ^ ((p - (n : ℝ)) / (p - 1)) := by
    funext x
    simp only [fundamentalPotential, if_neg hpne, radialPowerPotential]
  rw [heq]
  exact continuous_const.mul (continuous_norm.rpow_const (fun _ => Or.inr hq.le))

end BMCompactPDE
#print axioms BMCompactPDE.continuous_fundamentalPotential_supercritical
