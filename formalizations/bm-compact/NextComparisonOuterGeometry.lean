import WeakPDE
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Actual exterior tangent-ball geometry for the finite outer sphere. The
compact obstacle has a uniform positive separation from that tangent ball;
the empty obstacle is explicitly allowed. No trace or barrier is an input. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Metric
namespace BMCompactPDE

theorem exists_outer_sphere_tangent_ball_separated_from_compact
    {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) {R : ℝ} (hR : 0<R)
    (hKR : K⊆ball (0 : Space n) R) {a : Space n} (ha : ‖a‖=R) :
    ∃ z : Space n,∃ r L : ℝ,0<r ∧ r<L ∧ dist a z=r ∧
      ball (0 : Space n) R⊆(closedBall z r)ᶜ ∧ ∀ x∈K,L≤dist x z := by
  have hmargin : ∃ M : ℝ,M<R ∧ ∀ x∈K,‖x‖≤M := by
    by_cases hne : K.Nonempty
    · obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
      refine ⟨‖x‖,?_,fun y hy=>hmax hy⟩
      simpa only [mem_ball,dist_zero_right] using hKR hx
    · refine ⟨0,hR,?_⟩
      intro x hx
      exact False.elim (hne ⟨x,hx⟩)
  obtain ⟨M,hM,hMx⟩ := hmargin
  let z : Space n := (2 : ℝ) • a
  have hz : ‖z‖=2*R := by
    simp only [z,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : 0<(2 : ℝ)),ha]
  have ht (x : Space n) : 2*R≤dist x z+‖x‖ := by
    have h := dist_triangle z x (0 : Space n)
    simpa only [dist_zero_right,hz,dist_comm z x] using h
  refine ⟨z,R,2*R-M,hR,by linarith only [hM],?_,?_,?_⟩
  · have heq : a-z=-a := by
      dsimp only [z]
      rw [two_smul]
      abel
    rw [dist_eq_norm,heq,norm_neg,ha]
  · intro x hx
    have hxR : ‖x‖<R := by simpa only [mem_ball,dist_zero_right] using hx
    have hdist : R<dist x z := by linarith only [ht x,hxR]
    exact not_le.mpr hdist
  · intro x hx
    linarith only [ht x,hMx x hx]

end BMCompactPDE
#print axioms BMCompactPDE.exists_outer_sphere_tangent_ball_separated_from_compact
