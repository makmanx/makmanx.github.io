import RootManuscriptComparison

/-! Positive-source comparison with the weak comparator defined only on D.
The manuscript viscosity function is defined on a surrounding open set Ω.
The comparator is continuous on closure D; its PDE and differentiability are
required only in D. No extension across the Dirichlet boundary is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactPDE

theorem WeakPSourceSupersolutionPair.viscosity_le_on_own_domain
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)} {u v : Space n → ℝ}
    {g : Space n → Space n} (hv : WeakPSourceSupersolutionPair p c D v g)
    (hc : 0<c) (hvc : ContinuousOn v (closure D))
    (hvd : DifferentiableOn ℝ v D)
    (hv2 : ∀ z∈D, gradient v z≠0 → ContDiffAt ℝ 2 v z)
    (hu : BMCompactAnalytic.IsViscosityPSubsolution p Ω u)
    (hn : 2≤n) (hDb : Bornology.IsBounded D) (hDΩ : closure D⊆Ω)
    (hb : ∀ z∈frontier D,u z≤v z) : ∀ z∈D,u z≤v z := by
  intro a ha
  by_contra hnot
  have hgap : 0<u a-v a := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨k,hk,hs⟩ := exists_even_flat_contact_exponent hv.1
  let q : ℝ := ((2*k : ℕ) : ℝ)
  have hq : 1<q := by
    have hh : (2 : ℝ)≤(k : ℝ) := by exact_mod_cast hk
    dsimp only [q]
    push_cast
    linarith
  obtain ⟨j,hj,x,hx,y,hy,hpos,hm⟩ := exists_interior_doubled_power_maximum
    hv.2.1 hDb (hu.2.2.1.mono hDΩ) hvc hb ha hgap hq
  have hmD : ∀ z∈D,∀ w∈D,
      u z-v w-(j : ℝ)*criticalPowerPenalty q (z-w) ≤
        u x-v y-(j : ℝ)*criticalPowerPenalty q (x-y) :=
    fun z hz w hw=>hm z (subset_closure hz) w (subset_closure hw)
  have hxy := hv.ne_of_doubled_maximum hc (hvc.mono subset_closure)
    hn hq hs u (j : ℝ) hx hy hmD
  have hj0 : (j : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hyd : DifferentiableAt ℝ v y :=
    (hvd y hy).differentiableAt (hv.2.1.mem_nhds hy)
  have hgy := gradient_ne_zero_at_doubled_maximum hv.2.1 hq hj0 hx hy hxy hyd hmD
  have hy2 := hv2 y hy hgy
  let φ : Space n → ℝ := fun z=>v (z+y-x)+(u x-v y)
  have hφ2 : ContDiffAt ℝ 2 φ x :=
    BMCompactAnalytic.contDiffAt_diagonal_translate_add_const hy2 (u x-v y)
  obtain ⟨hφx,hupper⟩ := diagonal_upper_test_of_doubled_maximum hv.2.1 hx hy hmD
  have hφg : gradient φ x≠0 := by
    change gradient (fun z=>v (z+y-x)+(u x-v y)) x≠0
    rw [BMCompactAnalytic.gradient_diagonal_translate_add_const]
    exact hgy
  have huP := hu.2.2.2 x (hDΩ (subset_closure hx)) φ hφ2 hφx hupper hφg
  have hvP := hv.normalizedPLaplacian_neg_of_contDiffAt_two hc hn hy hy2 hgy
  change 0≤BMCompactAnalytic.normalizedPLaplacian p
    (fun z=>v (z+y-x)+(u x-v y)) x at huP
  rw [BMCompactAnalytic.normalizedPLaplacian_diagonal_translate_add_const] at huP
  exact (not_le_of_gt hvP) huP

theorem WeakPSourceSupersolutionPair.manuscript_le_on_own_domain
    {n : ℕ} {p c M : ℝ} {Ω D : Set (Space n)} {u v : Space n → ℝ}
    {g : Space n → Space n} (hv : WeakPSourceSupersolutionPair p c D v g)
    (hc : 0<c) (hvc : ContinuousOn v (closure D))
    (hvd : DifferentiableOn ℝ v D)
    (hv2 : ∀ z∈D, gradient v z≠0 → ContDiffAt ℝ 2 v z)
    (hu : BMCompactAnalytic.IsManuscriptViscosityPSubsolution p Ω u)
    (hub : ∀ z∈Ω,u z≤M) (hn : 2≤n)
    (hDb : Bornology.IsBounded D) (hDΩ : closure D⊆Ω)
    (hb : ∀ z∈frontier D,u z≤v z) : ∀ z∈D,u z≤v z := by
  exact hv.viscosity_le_on_own_domain hc hvc hvd hv2
    (hu.local_of_boundedAbove hub) hn hDb hDΩ hb

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.viscosity_le_on_own_domain
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.manuscript_le_on_own_domain
