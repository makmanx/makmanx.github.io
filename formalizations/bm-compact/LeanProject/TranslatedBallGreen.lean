import BallGreenExistence
import TranslatedBallWeak
import RadialTranslationLimit
import GreenAsymptoticBasics

/-! Actual Green witnesses for positive-radius balls with arbitrary centres.
The remainder is normalized against F(x), using the proved vanishing of
F(x-a)-F(x); translation of the asymptotic normalization is not assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology
namespace BMCompactPDE

theorem translatedBallGreen_hasGreenAsymptotic (n : ℕ) (σ : ℝ) {p R : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (a : Space n) :
    HasGreenAsymptotic n σ p (fun x : Space n => ballGreen n σ p R (x - a))
      (-fundamentalRadialValue n σ p R) := by
  have he : ∀ᶠ x in cobounded (Space n), R < ‖x - a‖ := by
    simpa only [dist_eq_norm] using
      (Metric.tendsto_dist_right_cobounded_atTop a).eventually (eventually_gt_atTop R)
  have htail : Tendsto
      (fun x : Space n => ballGreen n σ p R (x - a) - fundamentalPotential n σ p (x - a))
      (cobounded (Space n)) (nhds (-fundamentalRadialValue n σ p R)) := by
    apply (tendsto_const_nhds : Tendsto
      (fun _ : Space n => -fundamentalRadialValue n σ p R)
      (cobounded (Space n)) (nhds (-fundamentalRadialValue n σ p R))).congr'
    filter_upwards [he] with x hx
    rw [ballGreen_eq_profile_sub_of_le_norm n σ p R hx.le]
    ring
  have hsum := htail.add (tendsto_fundamentalPotential_translate_sub n σ hn hpn a)
  change Tendsto (fun x : Space n => ballGreen n σ p R (x - a) -
    fundamentalPotential n σ p x) (cobounded (Space n))
      (nhds (-fundamentalRadialValue n σ p R))
  have hsum' : Tendsto
      (fun x : Space n => (ballGreen n σ p R (x - a) - fundamentalPotential n σ p (x - a)) +
        (fundamentalPotential n σ p (x - a) - fundamentalPotential n σ p x))
      (cobounded (Space n)) (nhds (-fundamentalRadialValue n σ p R)) := by
    simpa only [add_zero] using hsum
  apply hsum'.congr'
  exact Eventually.of_forall (fun x => by ring)

theorem translatedBallGreen_isExteriorGreen (n : ℕ) {σ p R : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hR : 0 < R)
    (a : Space n) :
    IsExteriorGreen n σ p (Metric.closedBall a R)
      (fun x : Space n => ballGreen n σ p R (x - a)) := by
  refine ⟨hn, hpn, hσ, isCompact_closedBall _ _, ⟨a, by simpa using hR.le⟩,
    (continuous_ballGreen n σ p hR).comp (continuous_id.sub continuous_const), ?_,
    translatedBallGreen_isWeakPHarmonic n hσ hn hpn hR a,
    (translatedBallGreen_hasGreenAsymptotic n σ hn hpn a).boundedRemainder⟩
  intro x hx
  exact ballGreen_eq_zero_of_norm_le n σ p R
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)

theorem exists_translatedBallGreen_with_asymptotic (n : ℕ) {σ p R : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hR : 0 < R)
    (a : Space n) :
    ∃ G : Space n → ℝ, IsExteriorGreen n σ p (Metric.closedBall a R) G ∧
      HasGreenAsymptotic n σ p G (-fundamentalRadialValue n σ p R) :=
  ⟨fun x : Space n => ballGreen n σ p R (x - a),
    translatedBallGreen_isExteriorGreen n hσ hn hpn hR a,
    translatedBallGreen_hasGreenAsymptotic n σ hn hpn a⟩

end BMCompactPDE
#print axioms BMCompactPDE.translatedBallGreen_hasGreenAsymptotic
#print axioms BMCompactPDE.translatedBallGreen_isExteriorGreen
#print axioms BMCompactPDE.exists_translatedBallGreen_with_asymptotic
