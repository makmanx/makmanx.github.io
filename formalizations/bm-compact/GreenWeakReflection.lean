import GreenRigidOrder
import RigidWeakHarmonic

noncomputable section
open Set Metric
namespace BMCompactPDE

theorem IsExteriorGreen.separated_order_in_enclosing_ball {n : ℕ} {p σ : ℝ} {K : Set (Space n)}
    {G : Space n → ℝ} (hG : IsExteriorGreen n σ p K G)
    {R : ℝ} (hR : 0<R) (hRK : K⊆ball (0:Space n) R) :
    ∀ x y : Space n, ‖x‖+2*R≤‖y‖ → G x≤G y := by
  apply hG.separated_order_in_enclosing_ball_of_rigid_weak _ hR hRK
  obtain ⟨g,hg⟩ := hG.2.2.2.2.2.2.2.1
  intro e
  exact ⟨_,hg.comp_affine_isometry e⟩

theorem IsExteriorGreen.separated_order {n : ℕ} {p σ : ℝ} {K : Set (Space n)}
    {G : Space n → ℝ} (hG : IsExteriorGreen n σ p K G) :
    ∃ D:ℝ, 0<D ∧ ∀ x y : Space n, ‖x‖+D≤‖y‖ → G x≤G y := by
  obtain ⟨R,hR,hRK⟩ := hG.2.2.2.1.isBounded.subset_ball_lt 0 (0:Space n)
  exact ⟨2*R,by linarith,hG.separated_order_in_enclosing_ball hR hRK⟩

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.separated_order_in_enclosing_ball
#print axioms BMCompactPDE.IsExteriorGreen.separated_order
