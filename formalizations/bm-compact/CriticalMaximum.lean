import CriticalQuadratic

/-! The weak maximum principle for the actual noncritical-test viscosity
notion, valid also for comparison with a constant whose gradient is zero
everywhere. A strict quadratic with its centre outside the bounded domain
is an actual noncritical upper barrier; then its size tends to zero. This
does not establish comparison with arbitrary weak p-harmonic comparators. -/
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

theorem IsViscosityPSubsolution.leOn_const_of_boundary_order
    {p : ℝ} {Ω D : Set E} {u : E → ℝ} {c : ℝ}
    (hu : IsViscosityPSubsolution p Ω u)
    (hD : IsOpen D) (hDb : Bornology.IsBounded D) (hDO : closure D ⊆ Ω)
    (hboundary : ∀ x ∈ frontier D, u x ≤ c) :
    ∀ x ∈ D, u x ≤ c := by
  obtain ⟨R,hR,hbound⟩ := hDb.isCompact_closure.isBounded.exists_pos_norm_le
  obtain ⟨a,ha⟩ := NormedSpace.exists_lt_norm ℝ E R
  have hxa (x : E) (hx : x ∈ D) : x ≠ a := by
    intro heq
    have hb := hbound x (subset_closure hx)
    rw [heq] at hb
    exact (not_le_of_gt ha) hb
  let B : ℝ := (R+‖a‖)^2
  have hB : 0 ≤ B := sq_nonneg _
  have hdist (x : E) (hx : x ∈ closure D) : ‖x-a‖^2 ≤ B := by
    have hn : ‖x-a‖ ≤ R+‖a‖ :=
      (norm_sub_le x a).trans (add_le_add (hbound x hx) le_rfl)
    have hn0 := norm_nonneg (x-a)
    have hRa : 0 ≤ R+‖a‖ := by positivity
    dsimp only [B]
    nlinarith
  intro y hy
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε : ℝ := δ / (B+1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  have heq : ε*(B+1) = δ := by
    dsimp only [ε]
    exact div_mul_cancel₀ δ (by linarith)
  have hεB : ε*B ≤ δ := by nlinarith
  let h : E → ℝ := criticalQuadraticBarrier a ε (c+δ)
  have hCd : ContDiff ℝ ∞ h := contDiff_criticalQuadraticBarrier a ε (c+δ)
  have hCd2 : ContDiff ℝ 2 h := hCd.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfront : ∀ x ∈ frontier D, u x ≤ h x := by
    intro x hx
    have hxb := hdist x (frontier_subset_closure hx)
    have hb : ε*‖x-a‖^2 ≤ δ :=
      (mul_le_mul_of_nonneg_left hxb hε.le).trans hεB
    have hu0 := hboundary x hx
    dsimp only [h,criticalQuadraticBarrier]
    linarith
  have hcmp := hu.leOn_of_strict_classical_supersolution hD hDb hDO
    hCd.continuous.continuousOn hCd2.contDiffOn
    (fun x hx => gradient_criticalQuadraticBarrier_ne_zero hε (hxa x hx))
    (fun x hx => normalizedPLaplacian_criticalQuadraticBarrier_neg hu.1 hε (hxa x hx))
    hfront y hy
  have hh : h y ≤ c+δ := by
    dsimp only [h,criticalQuadraticBarrier]
    exact sub_le_self _ (mul_nonneg hε.le (sq_nonneg _))
  exact hcmp.trans hh

/-- The constant-comparator case with an ordinary nonpositive boundary
condition. Criticality of the constant is not ruled out or assumed away. -/
theorem IsViscosityPSubsolution.nonpos_of_boundary_nonpos
    {p : ℝ} {Ω D : Set E} {u : E → ℝ}
    (hu : IsViscosityPSubsolution p Ω u)
    (hD : IsOpen D) (hDb : Bornology.IsBounded D) (hDO : closure D ⊆ Ω)
    (hboundary : ∀ x ∈ frontier D, u x ≤ 0) :
    ∀ x ∈ D, u x ≤ 0 :=
  hu.leOn_const_of_boundary_order hD hDb hDO hboundary

end BMCompactAnalytic
#print axioms BMCompactAnalytic.IsViscosityPSubsolution.leOn_const_of_boundary_order
#print axioms BMCompactAnalytic.IsViscosityPSubsolution.nonpos_of_boundary_nonpos
