import UpstreamBoundaryPotential
import Geometry

/-! Genuine interior tangent-ball geometry of positive compact neighborhoods.
The ball is constructed at every point, including original points of K;
no boundary regularity or barrier/comparison statement is an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal Pointwise
namespace BMCompactPDE

theorem closedNeighborhood_has_interior_tangent_balls {n : ℕ} (hn : 0<n)
    {K : Set (Space n)} (hK : IsCompact K) {δ : ℝ} (hδ : 0<δ) :
    ∀ a∈BMCompact.closedNeighborhood δ K,∃ c : Space n,∃ R : ℝ,
      0<R ∧ closedBall c R⊆BMCompact.closedNeighborhood δ K ∧ dist a c=R := by
  intro a ha
  rw [BMCompact.closedNeighborhood_eq_add_closedBall hK hδ.le] at ha
  obtain ⟨y,hy,z,hz,rfl⟩ := mem_add.mp ha
  by_cases hz0 : z=0
  · subst z
    simp only [add_zero]
    let v : Space n := EuclideanSpace.basisFun (Fin n) ℝ ⟨0,hn⟩
    have hv : ‖v‖=1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one ⟨0,hn⟩
    let c : Space n := y+(δ/2) • v
    have hcy : dist c y=δ/2 := by
      simp only [c,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
        abs_of_pos (half_pos hδ),hv,mul_one]
    refine ⟨c,δ/2,half_pos hδ,?_,by rw [dist_comm,hcy]⟩
    intro t ht
    apply mem_cthickening_of_dist_le t y δ K hy
    have htc : dist t c≤δ/2 := mem_closedBall.mp ht
    have hty := dist_triangle t c y
    linarith only [htc,hty,hcy]
  · have hzpos : 0<‖z‖ := norm_pos_iff.mpr hz0
    have hzδ : ‖z‖≤δ := by simpa only [dist_zero_right] using mem_closedBall.mp hz
    refine ⟨y,‖z‖,hzpos,?_,?_⟩
    · intro t ht
      exact mem_cthickening_of_dist_le t y δ K hy ((mem_closedBall.mp ht).trans hzδ)
    · simp only [dist_eq_norm,add_sub_cancel_left]

end BMCompactPDE
#print axioms BMCompactPDE.closedNeighborhood_has_interior_tangent_balls
