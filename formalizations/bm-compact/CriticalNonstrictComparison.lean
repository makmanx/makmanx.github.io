import CriticalStrictificationCalc
import Mathlib.Analysis.Normed.Group.Bounded

/-! Non-strict comparison for actual C2 comparators with nonzero gradients.
Actual concave scalar transforms above the comparator converge uniformly to it
and have strictly negative operator. Critical comparator points are NOT covered
by this theorem; the constant-critical case is proved separately. -/
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem IsViscosityPSubsolution.leOn_of_nonstrict_noncritical_classical
    {p : ℝ} {Ω D : Set E} {u h : E → ℝ}
    (hu : IsViscosityPSubsolution p Ω u)
    (hD : IsOpen D) (hDb : Bornology.IsBounded D) (hDO : closure D ⊆ Ω)
    (hh : ContinuousOn h (closure D)) (hC2 : ContDiffOn ℝ 2 h D)
    (hg : ∀ x ∈ D, gradient h x ≠ 0)
    (hP : ∀ x ∈ D, normalizedPLaplacian p h x ≤ 0)
    (hboundary : ∀ x ∈ frontier D, u x ≤ h x) :
    ∀ x ∈ D, u x ≤ h x := by
  have hcompact := hDb.isCompact_closure
  obtain ⟨M0,hM0⟩ := hcompact.exists_bound_of_continuousOn hh
  let M : ℝ := max M0 0
  have hM (x : E) (hx : x ∈ closure D) : h x ≤ M :=
    (le_abs_self (h x)).trans ((hM0 x hx).trans (le_max_left _ _))
  have hsq : ContinuousOn (fun x => (h x-M)^2) (closure D) :=
    (hh.sub continuousOn_const).pow 2
  obtain ⟨K0,hK0⟩ := hcompact.exists_bound_of_continuousOn hsq
  let K : ℝ := max K0 0
  have hK : 0 ≤ K := le_max_right _ _
  have hs (x : E) (hx : x ∈ closure D) : (h x-M)^2 ≤ K :=
    (le_abs_self ((h x-M)^2)).trans ((hK0 x hx).trans (le_max_left _ _))
  intro y hy
  apply le_of_forall_pos_le_add
  intro δ hδ
  let τ : ℝ := δ/(K+1)
  have hτ : 0 < τ := div_pos hδ (by linarith)
  have hτeq : τ*(K+1)=δ := by
    dsimp only [τ]
    exact div_mul_cancel₀ δ (by linarith)
  have hτK : τ*K ≤ δ := by nlinarith
  let H : E → ℝ := criticalConcaveTransform τ K M h
  have hHc : ContinuousOn H (closure D) :=
    hh.add (continuousOn_const.mul (continuousOn_const.sub hsq))
  have hHC2 : ContDiffOn ℝ 2 H D := by
    intro x hx
    exact (contDiffAt_criticalConcaveTransform (hC2.contDiffAt (hD.mem_nhds hx))).contDiffWithinAt
  have hHg (x : E) (hx : x ∈ D) : gradient H x ≠ 0 := by
    rw [gradient_criticalConcaveTransform
      ((hC2.contDiffAt (hD.mem_nhds hx)).differentiableAt (by norm_num))]
    exact smul_ne_zero (criticalConcaveSlope_pos hτ (hM x (subset_closure hx))).ne' (hg x hx)
  have hHP (x : E) (hx : x ∈ D) : normalizedPLaplacian p H x < 0 :=
    normalizedPLaplacian_criticalConcaveTransform_neg hu.1 hτ
      (hC2.contDiffAt (hD.mem_nhds hx)) (hg x hx) (hM x (subset_closure hx)) (hP x hx)
  have hHb (x : E) (hx : x ∈ frontier D) : u x ≤ H x := by
    have hxs := hs x (frontier_subset_closure hx)
    have hnon : 0 ≤ τ*(K-(h x-M)^2) := mul_nonneg hτ.le (sub_nonneg.mpr hxs)
    have hb := hboundary x hx
    dsimp only [H,criticalConcaveTransform]
    linarith
  have hcmp := hu.leOn_of_strict_classical_supersolution hD hDb hDO
    hHc hHC2 hHg hHP hHb y hy
  have hupper : H y ≤ h y+δ := by
    have hnon := sq_nonneg (h y-M)
    have ht : τ*(K-(h y-M)^2) ≤ τ*K :=
      mul_le_mul_of_nonneg_left (sub_le_self _ hnon) hτ.le
    dsimp only [H,criticalConcaveTransform]
    linarith
  exact hcmp.trans hupper

/-- Actual weak p-harmonicity supplies the comparator equation. The C2 and
nonzero-gradient assumptions remain explicit and are not general regularity. -/
theorem IsViscosityPSubsolution.leOn_of_weak_C2_noncritical
    {n : ℕ} {p : ℝ} {Ω D : Set (BMCompactPDE.Space n)}
    {u h : BMCompactPDE.Space n → ℝ}
    (hu : IsViscosityPSubsolution p Ω u)
    (hD : IsOpen D) (hDb : Bornology.IsBounded D) (hDO : closure D ⊆ Ω)
    (hh : ContinuousOn h (closure D)) (hC2 : ContDiffOn ℝ 2 h D)
    (hw : BMCompactPDE.IsWeakPHarmonic p D h)
    (hg : ∀ x ∈ D, gradient h x ≠ 0)
    (hboundary : ∀ x ∈ frontier D, u x ≤ h x) :
    ∀ x ∈ D, u x ≤ h x := by
  apply hu.leOn_of_nonstrict_noncritical_classical hD hDb hDO hh hC2 hg _ hboundary
  intro x hx
  have heq := hw.classicalPLaplacian_eq_zero_of_contDiffAt_two hx
    (hC2.contDiffAt (hD.mem_nhds hx)) (hg x hx)
  exact (normalizedPLaplacian_eq_zero_of_classical_eq_zero (hg x hx) heq).le

end BMCompactAnalytic
#print axioms BMCompactAnalytic.IsViscosityPSubsolution.leOn_of_nonstrict_noncritical_classical
#print axioms BMCompactAnalytic.IsViscosityPSubsolution.leOn_of_weak_C2_noncritical
