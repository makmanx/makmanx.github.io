import TranslatedBallGreen
import UpstreamBoundaryGreenUnique
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! Theorem C(a), critical case, for two closed balls with independent positive
radii and arbitrary centres. The witnesses solve the actual exterior weak PDE
and uniqueness allows arbitrary choices of the three Green functions. -/
noncomputable section
open Set Metric
open scoped Pointwise
namespace BMCompactPDE

theorem weighted_closedBalls {n : ℕ} (a b : Space n) {r s t : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t • closedBall a r + (1-t) • closedBall b s =
      closedBall (t • a + (1-t) • b) (t*r + (1-t)*s) := by
  have hu := sub_nonneg.mpr ht1
  rw [smul_closedBall t a hr, smul_closedBall (1-t) b hs,
    Real.norm_of_nonneg ht, Real.norm_of_nonneg hu,
    closedBall_add_closedBall (mul_nonneg ht hr) (mul_nonneg hu hs)]

theorem weighted_ball_radius_pos {r s t : ℝ} (hr : 0 < r) (hs : 0 < s)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : 0 < t*r + (1-t)*s := by
  rcases eq_or_lt_of_le ht with he | he
  · simp [← he, hs]
  · exact add_pos_of_pos_of_nonneg (mul_pos he hr) (mul_nonneg (sub_nonneg.mpr ht1) hs.le)

private def ballRatio {n : ℕ} (r : ℝ) (x : Space n) : ℝ := max r ‖x‖ / r

private theorem ballRatio_one_le {n : ℕ} {r : ℝ} (hr : 0 < r) (x : Space n) :
    1 ≤ ballRatio r x := (one_le_div hr).2 (le_max_left _ _)

private theorem ballRatio_mix {n : ℕ} {r s t : ℝ} (hr : 0 < r) (hs : 0 < s)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (x y : Space n) :
    ballRatio (t*r+(1-t)*s) (t • x + (1-t) • y) ≤ max (ballRatio r x) (ballRatio s y) := by
  let M := max (ballRatio r x) (ballRatio s y)
  have hm : 1 ≤ M := (ballRatio_one_le hr x).trans (le_max_left _ _)
  have hr' : ‖x‖ ≤ M*r := (le_max_right r ‖x‖).trans ((div_le_iff₀ hr).mp (le_max_left (ballRatio r x) _))
  have hs' : ‖y‖ ≤ M*s := (le_max_right s ‖y‖).trans ((div_le_iff₀ hs).mp (le_max_right _ (ballRatio s y)))
  have hR := weighted_ball_radius_pos hr hs ht ht1
  have hu := sub_nonneg.mpr ht1
  apply (div_le_iff₀ hR).2
  apply max_le
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hm hR.le
  · calc
      ‖t • x + (1-t) • y‖ ≤ ‖t • x‖ + ‖(1-t) • y‖ := norm_add_le _ _
      _ = t*‖x‖ + (1-t)*‖y‖ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg ht, Real.norm_of_nonneg hu]
      _ ≤ t*(M*r) + (1-t)*(M*s) := add_le_add (mul_le_mul_of_nonneg_left hr' ht) (mul_le_mul_of_nonneg_left hs' hu)
      _ = M*(t*r+(1-t)*s) := by ring

private theorem critical_ballGreen_ratio {n : ℕ} (σ : ℝ) {r : ℝ}
    (hr : 0 < r) (x : Space n) :
    ballGreen n σ n r x = σ ^ (-((n:ℝ)-1)⁻¹) * Real.log (ballRatio r x) := by
  have hx : 0 < max r ‖x‖ := hr.trans_le (le_max_left _ _)
  simp only [ballGreen, fundamentalRadialValue, fundamentalPotential, ite_true,
    criticalRadialPotential, Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hr, ballRatio,
    Real.log_div hx.ne' hr.ne']
  ring

private theorem critical_ballGreen_mix {n : ℕ} {σ r s t : ℝ}
    (hσ : 0 < σ) (hr : 0 < r) (hs : 0 < s) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (x y : Space n) :
    ballGreen n σ n (t*r+(1-t)*s) (t • x + (1-t) • y) ≤
      max (ballGreen n σ n r x) (ballGreen n σ n s y) := by
  have hR := weighted_ball_radius_pos hr hs ht ht1
  have ha := ballRatio_mix hr hs ht ht1 x y
  have hpos := zero_lt_one.trans_le (ballRatio_one_le hR (t • x + (1-t) • y))
  rw [critical_ballGreen_ratio σ hR, critical_ballGreen_ratio σ hr, critical_ballGreen_ratio σ hs]
  rcases le_total (ballRatio r x) (ballRatio s y) with h | h
  · rw [max_eq_right h] at ha
    exact (mul_le_mul_of_nonneg_left (Real.log_le_log hpos ha) (Real.rpow_nonneg hσ.le _)).trans (le_max_right _ _)
  · rw [max_eq_left h] at ha
    exact (mul_le_mul_of_nonneg_left (Real.log_le_log hpos ha) (Real.rpow_nonneg hσ.le _)).trans (le_max_left _ _)

/-- Arbitrary actual critical exterior Green functions of positive-radius
balls and their Minkowski combination satisfy Theorem C(a). -/
theorem theoremC_critical_closedBalls {n : ℕ} {σ r s t : ℝ}
    (hn : 1 < (n : ℝ)) (hσ : 0 < σ) (hr : 0 < r) (hs : 0 < s)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (a b : Space n) {G H L : Space n → ℝ}
    (hG : IsExteriorGreen n σ n (closedBall a r) G)
    (hH : IsExteriorGreen n σ n (closedBall b s) H)
    (hL : IsExteriorGreen n σ n (t • closedBall a r + (1-t) • closedBall b s) L)
    (x y : Space n) : L (t • x + (1-t) • y) ≤ max (G x) (H y) := by
  have hR := weighted_ball_radius_pos hr hs ht ht1
  rw [weighted_closedBalls a b hr.le hs.le ht ht1] at hL
  rw [hG.unique (translatedBallGreen_isExteriorGreen n hσ hn le_rfl hr a),
    hH.unique (translatedBallGreen_isExteriorGreen n hσ hn le_rfl hs b),
    hL.unique (translatedBallGreen_isExteriorGreen n hσ hn le_rfl hR _)]
  have he : t • x + (1-t) • y - (t • a + (1-t) • b) = t • (x-a) + (1-t) • (y-b) := by
    simp only [smul_sub]
    abel
  simpa only [he] using critical_ballGreen_mix hσ hr hs ht ht1 (x-a) (y-b)

/-- The three Green functions and their pointwise comparison are constructed
from just the balls, dimension and normalization. -/
theorem exists_critical_closedBalls_Green_comparison {n : ℕ} {σ r s t : ℝ}
    (hn : 1 < (n : ℝ)) (hσ : 0 < σ) (hr : 0 < r) (hs : 0 < s)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (a b : Space n) :
    ∃ G H L : Space n → ℝ, IsExteriorGreen n σ n (closedBall a r) G ∧
      IsExteriorGreen n σ n (closedBall b s) H ∧
      IsExteriorGreen n σ n (t • closedBall a r + (1-t) • closedBall b s) L ∧
      ∀ x y, L (t • x + (1-t) • y) ≤ max (G x) (H y) := by
  obtain ⟨G,hG,_⟩ := exists_translatedBallGreen_with_asymptotic n hσ hn le_rfl hr a
  obtain ⟨H,hH,_⟩ := exists_translatedBallGreen_with_asymptotic n hσ hn le_rfl hs b
  obtain ⟨L,hL,_⟩ := exists_translatedBallGreen_with_asymptotic n hσ hn le_rfl
    (weighted_ball_radius_pos hr hs ht ht1) (t • a + (1-t) • b)
  rw [← weighted_closedBalls a b hr.le hs.le ht ht1] at hL
  exact ⟨G,H,L,hG,hH,hL,theoremC_critical_closedBalls hn hσ hr hs ht ht1 a b hG hH hL⟩

end BMCompactPDE
#print axioms BMCompactPDE.weighted_closedBalls
#print axioms BMCompactPDE.weighted_ball_radius_pos
#print axioms BMCompactPDE.theoremC_critical_closedBalls

#print axioms BMCompactPDE.exists_critical_closedBalls_Green_comparison
