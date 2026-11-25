import GreenDefs
import RadialRegularity
import Mathlib.Tactic.Linarith

/-! Analytic and asymptotic parts of the explicit closed-ball Green candidate.
Weak p-harmonicity is proved separately; no general Green theorem is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology

namespace BMCompactPDE

theorem fundamentalPotential_norm (n : ℕ) (σ p : ℝ) (x : Space n) :
    fundamentalRadialValue n σ p ‖x‖ = fundamentalPotential n σ p x := by
  simp [fundamentalRadialValue, fundamentalPotential, criticalRadialPotential,
    radialPowerPotential]

theorem ballGreen_eq_zero_of_norm_le (n : ℕ) (σ p R : ℝ) {x : Space n}
    (hx : ‖x‖ ≤ R) : ballGreen n σ p R x = 0 := by
  simp [ballGreen, max_eq_left hx]

theorem ballGreen_eq_profile_sub_of_le_norm (n : ℕ) (σ p R : ℝ) {x : Space n}
    (hx : R ≤ ‖x‖) :
    ballGreen n σ p R x = fundamentalPotential n σ p x - fundamentalRadialValue n σ p R := by
  rw [ballGreen, max_eq_right hx, fundamentalPotential_norm]

theorem continuous_ballGreen (n : ℕ) (σ p : ℝ) {R : ℝ} (hR : 0 < R) :
    Continuous (ballGreen n σ p R) := by
  change Continuous (fun x : Space n => fundamentalRadialValue n σ p (max R ‖x‖) -
    fundamentalRadialValue n σ p R)
  have hcomp : Continuous (fun x : Space n => fundamentalRadialValue n σ p (max R ‖x‖)) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hpos : 0 < max R ‖x‖ := hR.trans_le (le_max_left _ _)
    have hc : ContinuousAt (fundamentalRadialValue n σ p) (max R ‖x‖) :=
      (contDiffAt_fundamentalPotential n σ p (ne_of_gt hpos)).continuousAt
    have hi : ContinuousAt (fun y : Space n => max R ‖y‖) x :=
      (continuous_const.max continuous_norm).continuousAt
    exact ContinuousAt.comp (f := fun y : Space n => max R ‖y‖) hc hi
  exact hcomp.sub continuous_const

theorem ballGreen_zero_on_closedBall (n : ℕ) (σ p R : ℝ) :
    EqOn (ballGreen n σ p R) (fun _ => 0) (Metric.closedBall (0 : Space n) R) := by
  intro x hx
  exact ballGreen_eq_zero_of_norm_le n σ p R (by simpa using hx)

theorem eventually_ballGreen_remainder_eq (n : ℕ) (σ p R : ℝ) :
    ∀ᶠ x in cobounded (Space n),
      ballGreen n σ p R x - fundamentalPotential n σ p x =
        - fundamentalRadialValue n σ p R := by
  have he : ∀ᶠ x in cobounded (Space n), R < ‖x‖ := by
    simpa using (Metric.tendsto_dist_right_cobounded_atTop (0 : Space n)).eventually
      (eventually_gt_atTop R)
  filter_upwards [he] with x hx
  rw [ballGreen_eq_profile_sub_of_le_norm n σ p R hx.le]
  ring

theorem ballGreen_hasBoundedGreenRemainder (n : ℕ) (σ p R : ℝ) :
    HasBoundedGreenRemainder n σ p (ballGreen n σ p R) := by
  refine ⟨|fundamentalRadialValue n σ p R|, abs_nonneg _, ?_⟩
  filter_upwards [eventually_ballGreen_remainder_eq n σ p R] with x hx
  rw [hx, abs_neg]

theorem ballGreen_hasGreenAsymptotic (n : ℕ) (σ p R : ℝ) :
    HasGreenAsymptotic n σ p (ballGreen n σ p R)
      (-fundamentalRadialValue n σ p R) := by
  apply (tendsto_const_nhds : Tendsto
    (fun _ : Space n => -fundamentalRadialValue n σ p R)
    (cobounded (Space n)) (nhds (-fundamentalRadialValue n σ p R))).congr'
  have heq : (fun x : Space n => ballGreen n σ p R x - fundamentalPotential n σ p x)
      =ᶠ[cobounded (Space n)] (fun _ => -fundamentalRadialValue n σ p R) :=
    eventually_ballGreen_remainder_eq n σ p R
  exact heq.symm

end BMCompactPDE

#print axioms BMCompactPDE.fundamentalPotential_norm
#print axioms BMCompactPDE.ballGreen_eq_zero_of_norm_le
#print axioms BMCompactPDE.ballGreen_eq_profile_sub_of_le_norm
#print axioms BMCompactPDE.continuous_ballGreen
#print axioms BMCompactPDE.ballGreen_zero_on_closedBall
#print axioms BMCompactPDE.eventually_ballGreen_remainder_eq
#print axioms BMCompactPDE.ballGreen_hasBoundedGreenRemainder
#print axioms BMCompactPDE.ballGreen_hasGreenAsymptotic
