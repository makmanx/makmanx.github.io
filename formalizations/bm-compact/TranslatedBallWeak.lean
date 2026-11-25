import BallGreenExistence
import TranslatedRadialWeak

/-! The actual zero-boundary ball profile is weak p-harmonic outside a ball
with any centre, by the proved smooth radial translation and function congruence.
The normalization at infinity is handled separately. -/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology
namespace BMCompactPDE

theorem translatedBallGreen_isWeakPHarmonic (n : ℕ) {σ p R : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hR : 0 < R)
    (a : Space n) :
    IsWeakPHarmonic p (Metric.closedBall a R)ᶜ
      (fun x : Space n => ballGreen n σ p R (x - a)) := by
  have hΩ : IsOpen ((Metric.closedBall a R)ᶜ) := Metric.isClosed_closedBall.isOpen_compl
  have hΩa : (Metric.closedBall a R)ᶜ ⊆ {x : Space n | x ≠ a} := by
    intro x hx hxa
    apply hx
    simpa [hxa] using hR.le
  have hf := (isWeakPHarmonic_fundamentalPotential_sub n hσ hn hpn a).mono hΩa hΩ
  apply (hf.sub_const (fundamentalRadialValue n σ p R)).congr_on
  intro x hx
  have hRnorm : R < ‖x - a‖ := by
    apply lt_of_not_ge
    intro h
    exact hx (by simpa only [Metric.mem_closedBall, dist_eq_norm] using h)
  exact (ballGreen_eq_profile_sub_of_le_norm n σ p R hRnorm.le).symm

end BMCompactPDE
#print axioms BMCompactPDE.translatedBallGreen_isWeakPHarmonic
