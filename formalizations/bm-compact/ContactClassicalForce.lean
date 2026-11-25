import ContactFlatPower

/-! Source inequalities at ordinary non-strict lower contacts and actual
noncritical C2 points. Subtracting the actual quartic makes contact strict
without changing its gradient or p-Laplacian. This derives the forced
classical inequality from the actual weak representative and field; it does
not assume the field was already the classical gradient. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem gradient_sub_strictContactQuartic_self {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) :
    gradient (fun y => φ y-strictContactQuartic x y) x=gradient φ x := by
  unfold gradient
  rw [fderiv_fun_sub hφ ((contDiff_strictContactQuartic x).differentiable (by simp) x),
    fderiv_strictContactQuartic_self,sub_zero]

theorem normalizedPLaplacian_sub_strictContactQuartic_self (p : ℝ)
    {φ : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ x) :
    normalizedPLaplacian p (fun y => φ y-strictContactQuartic x y) x=
      normalizedPLaplacian p φ x := by
  have hq : ContDiffAt ℝ 2 (strictContactQuartic x) x :=
    ((contDiff_strictContactQuartic x).of_le (by decide)).contDiffAt
  have he := normalizedPLaplacian_add_strictContactQuartic_self p (hφ.sub hq)
  simpa only [sub_add_cancel] using he.symm

theorem classicalPLaplacian_sub_strictContactQuartic_self (p : ℝ)
    {φ : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ x) :
    classicalPLaplacian p (fun y => φ y-strictContactQuartic x y) x=
      classicalPLaplacian p φ x := by
  simp only [classicalPLaplacian,
    gradient_sub_strictContactQuartic_self (hφ.differentiableAt (by norm_num)),
    normalizedPLaplacian_sub_strictContactQuartic_self p hφ]

end BMCompactAnalytic
namespace BMCompactPDE

theorem WeakPSourceSupersolutionPair.le_neg_classicalPLaplacian_at_nonstrict_contact
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : WeakPSourceSupersolutionPair p c Ω v h) (hvc : ContinuousOn v Ω)
    (hn : 2≤n) {x : Space n} (hx : x∈Ω)
    {φ : Space n → ℝ} (hφ : ContDiffOn ℝ 2 φ Ω)
    (htouch : v x=φ x) (hbelow : ∀ y∈Ω, φ y≤v y)
    (hg : gradient φ x≠0) : c ≤ -BMCompactAnalytic.classicalPLaplacian p φ x := by
  let ψ : Space n → ℝ := fun y => φ y-BMCompactAnalytic.strictContactQuartic x y
  have hq : ContDiff ℝ 2 (BMCompactAnalytic.strictContactQuartic x : Space n → ℝ) :=
    (BMCompactAnalytic.contDiff_strictContactQuartic x).of_le (by decide)
  have hψ : ContDiffOn ℝ 2 ψ Ω := hφ.sub hq.contDiffOn
  have hψx : ψ x=φ x := by
    dsimp only [ψ]
    rw [BMCompactAnalytic.strictContactQuartic_self,sub_zero]
  have hstrict : ∀ y∈Ω, y≠x → ψ y<v y := by
    intro y hy hne
    have hb := hbelow y hy
    have hpos := BMCompactAnalytic.strictContactQuartic_pos hne
    dsimp only [ψ]
    linarith
  have hφat := hφ.contDiffAt (hv.2.1.mem_nhds hx)
  have hgrad : gradient ψ x=gradient φ x :=
    BMCompactAnalytic.gradient_sub_strictContactQuartic_self (hφat.differentiableAt (by norm_num))
  have he := hv.le_neg_classicalPLaplacian_at_strict_contact hvc hn hx hψ
    (htouch.trans hψx.symm) hstrict (by rw [hgrad];exact hg)
  simpa only [ψ,BMCompactAnalytic.classicalPLaplacian_sub_strictContactQuartic_self p hφat] using he

/-- Actual forced weak supersolutions satisfy the genuine classical operator
inequality at every C2 noncritical point. No pre-identified weak gradient,
classical equation, viscosity predicate or comparison premise is supplied. -/
theorem WeakPSourceSupersolutionPair.classicalPLaplacian_le_neg_source
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : WeakPSourceSupersolutionPair p c Ω v h) (hvc : ContDiffOn ℝ 2 v Ω)
    (hn : 2≤n) {x : Space n} (hx : x∈Ω) (hg : gradient v x≠0) :
    BMCompactAnalytic.classicalPLaplacian p v x ≤ -c := by
  have he := hv.le_neg_classicalPLaplacian_at_nonstrict_contact hvc.continuousOn hn hx hvc
    rfl (fun _ _ => le_rfl) hg
  linarith


theorem WeakPSourceSupersolutionPair.classicalPLaplacian_le_neg_source_of_contDiffAt_two
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : WeakPSourceSupersolutionPair p c Ω v h) (hn : 2≤n)
    {x : Space n} (hx : x∈Ω) (hv2 : ContDiffAt ℝ 2 v x) (hg : gradient v x≠0) :
    BMCompactAnalytic.classicalPLaplacian p v x ≤ -c := by
  obtain ⟨U,hUn,hvU⟩ := hv2.contDiffOn le_rfl (by simp)
  obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hUn
  have hW := hv.mono (U := Ω ∩ V) inter_subset_left (hv.2.1.inter hV)
  exact hW.classicalPLaplacian_le_neg_source
    (hvU.mono (inter_subset_right.trans hVU)) hn ⟨hx,hxV⟩ hg

theorem WeakPSourceSupersolutionPair.normalizedPLaplacian_neg_of_contDiffAt_two
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : WeakPSourceSupersolutionPair p c Ω v h) (hc : 0<c) (hn : 2≤n)
    {x : Space n} (hx : x∈Ω) (hv2 : ContDiffAt ℝ 2 v x) (hg : gradient v x≠0) :
    BMCompactAnalytic.normalizedPLaplacian p v x<0 := by
  have he := hv.classicalPLaplacian_le_neg_source_of_contDiffAt_two hn hx hv2 hg
  have hp : 0<‖gradient v x‖^(p-2) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hg) _
  by_contra hnonn
  have hprod := mul_nonneg hp.le (le_of_not_gt hnonn)
  change ‖gradient v x‖^(p-2)*BMCompactAnalytic.normalizedPLaplacian p v x≤-c at he
  linarith

end BMCompactPDE
#print axioms BMCompactAnalytic.gradient_sub_strictContactQuartic_self
#print axioms BMCompactAnalytic.normalizedPLaplacian_sub_strictContactQuartic_self
#print axioms BMCompactAnalytic.classicalPLaplacian_sub_strictContactQuartic_self
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.le_neg_classicalPLaplacian_at_nonstrict_contact
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.classicalPLaplacian_le_neg_source
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.classicalPLaplacian_le_neg_source_of_contDiffAt_two
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.normalizedPLaplacian_neg_of_contDiffAt_two
