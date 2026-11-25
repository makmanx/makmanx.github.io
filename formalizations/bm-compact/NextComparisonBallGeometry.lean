import WeakPDE
import Mathlib.Tactic.Linarith

/-! The actual strict radial separation of an inner closed ball contained in
an origin-centered open ball. A farthest radial point is constructed, including
the zero-center case. No geometric separation is an input. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Metric
namespace BMCompactPDE

theorem norm_add_radius_lt_of_closedBall_subset_ball_zero
    {n : ℕ} (hn : 0<n) (z : Space n) {r R : ℝ} (hr : 0<r)
    (hsub : closedBall z r⊆ball (0 : Space n) R) : ‖z‖+r<R := by
  by_cases hz : z=0
  · subst z
    let e : Space n := EuclideanSpace.basisFun (Fin n) ℝ ⟨0,hn⟩
    have he : ‖e‖=1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one ⟨0,hn⟩
    have hnorm : ‖r • e‖=r := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,he,mul_one]
    have hx : r • e∈closedBall (0 : Space n) r := by
      simpa only [mem_closedBall,dist_zero_right,hnorm] using (le_refl r)
    have hR := hsub hx
    simpa only [mem_ball,dist_zero_right,hnorm,norm_zero,zero_add] using hR
  · have hzn : 0<‖z‖ := norm_pos_iff.mpr hz
    let t : ℝ := r/‖z‖
    have ht : 0<t := div_pos hr hzn
    let x : Space n := (1+t) • z
    have hxsub : x-z=t • z := by
      simp only [x,add_smul,one_smul,add_sub_cancel_left]
    have hxd : ‖x-z‖=r := by
      rw [hxsub,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
      exact div_mul_cancel₀ r hzn.ne'
    have hxn : ‖x‖=‖z‖+r := by
      dsimp only [x]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith only [ht] : 0<1+t)]
      dsimp only [t]
      rw [add_mul,one_mul,div_mul_cancel₀ r hzn.ne']
    have hx : x∈closedBall z r := by
      simpa only [mem_closedBall,dist_eq_norm,hxd] using (le_refl r)
    have hR := hsub hx
    simpa only [mem_ball,dist_zero_right,hxn] using hR

end BMCompactPDE
#print axioms BMCompactPDE.norm_add_radius_lt_of_closedBall_subset_ball_zero
