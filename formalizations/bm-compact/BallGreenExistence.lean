import BallGreenCore
import RadialWeakHarmonic
import WeakAffine

/-! Genuine Green witnesses for positive-radius closed balls, with the concrete
weak p-Laplace equation and the exact finite asymptotic constant. The parameter
σ still awaits identification with Hausdorff sphere area. No general compact
Green existence or uniqueness theorem is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology

namespace BMCompactPDE

theorem ballGreen_isWeakPHarmonic (n : ℕ) {σ p R : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hR : 0 < R) :
    IsWeakPHarmonic p (Metric.closedBall (0 : Space n) R)ᶜ (ballGreen n σ p R) := by
  have hΩ : IsOpen ((Metric.closedBall (0 : Space n) R)ᶜ) :=
    Metric.isClosed_closedBall.isOpen_compl
  have hΩ0 : (Metric.closedBall (0 : Space n) R)ᶜ ⊆ {x : Space n | x ≠ 0} := by
    intro x hx hzero
    apply hx
    simpa [hzero] using hR.le
  have hf := (isWeakPHarmonic_fundamentalPotential n hσ hn hpn).mono hΩ0 hΩ
  apply (hf.sub_const (fundamentalRadialValue n σ p R)).congr_on
  intro x hx
  have hRnorm : R < ‖x‖ := by
    apply lt_of_not_ge
    intro h
    exact hx (by simpa using h)
  exact (ballGreen_eq_profile_sub_of_le_norm n σ p R hRnorm.le).symm

theorem ballGreen_isExteriorGreen (n : ℕ) {σ p R : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hR : 0 < R) :
    IsExteriorGreen n σ p (Metric.closedBall (0 : Space n) R) (ballGreen n σ p R) := by
  refine ⟨hn, hpn, hσ, isCompact_closedBall _ _, ?_, continuous_ballGreen n σ p hR,
    ballGreen_zero_on_closedBall n σ p R, ballGreen_isWeakPHarmonic n hσ hn hpn hR,
    ballGreen_hasBoundedGreenRemainder n σ p R⟩
  exact ⟨0, by simpa using hR.le⟩

theorem exists_ballGreen_with_asymptotic (n : ℕ) {σ p R : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hR : 0 < R) :
    ∃ G : Space n → ℝ,
      IsExteriorGreen n σ p (Metric.closedBall (0 : Space n) R) G ∧
      HasGreenAsymptotic n σ p G (-fundamentalRadialValue n σ p R) :=
  ⟨ballGreen n σ p R, ballGreen_isExteriorGreen n hσ hn hpn hR,
    ballGreen_hasGreenAsymptotic n σ p R⟩

end BMCompactPDE

#print axioms BMCompactPDE.ballGreen_isWeakPHarmonic
#print axioms BMCompactPDE.ballGreen_isExteriorGreen
#print axioms BMCompactPDE.exists_ballGreen_with_asymptotic
