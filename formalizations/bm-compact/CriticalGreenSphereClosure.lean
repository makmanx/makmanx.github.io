import GreenRemainderEnclosure

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology
namespace BMCompactPDE

/-- A subsequence of small oscillations on the radius-four sphere of the
rescaled data determines the finite exterior constant in physical space. -/
theorem IsExteriorGreen.exists_finite_critical_asymptotic_of_rescaled_sphere_oscillation
    {n : ℕ} {σ : ℝ} {K : Set (Space n)} {u : Space n → ℝ}
    (hu : IsExteriorGreen n σ n K u)
    {R : ℕ → ℝ} (hR : ∀ j, 0<R j) (hRlim : Tendsto R atTop atTop)
    (hosc : ∀ ε : ℝ, 0<ε → ∀ N : ℕ, ∃ j≥N, ∀ x y : Space n, ‖x‖=4 → ‖y‖=4 →
      |(u (R j • x)-fundamentalPotential n σ n (R j • x))-
       (u (R j • y)-fundamentalPotential n σ n (R j • y))|<ε) :
    ∃ c : ℝ, HasGreenAsymptotic n σ n u c := by
  have hn : 1<n := by exact_mod_cast hu.1
  let v : Space n := (4:ℝ) • EuclideanSpace.basisFun (Fin n) ℝ ⟨0,by omega⟩
  have hv : ‖v‖=4 := by
    simp only [v,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<4),
      (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one,mul_one]
  have hK := hu.2.2.2.1
  obtain ⟨s,_,hKs⟩ := hK.isBounded.subset_ball_lt 0 (0:Space n)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hRlim.eventually (eventually_ge_atTop s))
  apply hu.exists_finite_asymptotic_of_small_enclosing_frontiers
  intro ε hε
  obtain ⟨j,hj,hsmall⟩ := hosc (ε/3) (by linarith only [hε]) N
  let t := 4*R j
  have ht : 0<t := mul_pos (by norm_num) (hR j)
  let E := closedBall (0:Space n) t
  have hKE : K⊆E := hKs.trans ((ball_subset_ball (show s≤t by
    dsimp [t];linarith only [hN j hj,hR j])).trans ball_subset_closedBall)
  let c := u (R j • v)-fundamentalPotential n σ n (R j • v)
  refine ⟨E,isCompact_closedBall _ _,hKE,⟨t,ht,subset_rfl⟩,
    c-ε/3,c+ε/3,by linarith only [hε],?_⟩
  intro x hx
  have hxnorm : ‖x‖=4*R j := by
    simpa only [mem_sphere,dist_zero_right] using (frontier_closedBall_subset_sphere hx)
  let y := (R j)⁻¹ • x
  have hyn : ‖y‖=4 := by
    rw [show ‖y‖= (R j)⁻¹ * ‖x‖ by simp only [y,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hR j))],
      hxnorm,mul_comm (4:ℝ) (R j),←mul_assoc,inv_mul_cancel₀ (hR j).ne',one_mul]
  have heq : R j • y = x := by simp only [y,smul_smul,mul_inv_cancel₀ (hR j).ne',one_smul]
  have hh := hsmall y v hyn hv
  rw [heq] at hh
  change |(u x-fundamentalPotential n σ n x)-c|<ε/3 at hh
  constructor <;> linarith only [(abs_lt.mp hh).1,(abs_lt.mp hh).2]

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.exists_finite_critical_asymptotic_of_rescaled_sphere_oscillation
