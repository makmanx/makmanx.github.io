import SuperC1Boundary

/-! Boundary comparison does not require C1 extension through the boundary or
finite energy on the whole domain. Compact epsilon-excess localization reduces
to genuine relatively compact weak sub/supersolution comparison. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace BMCompactPDE

theorem WeakPSubsolutionPair.leOn_of_C1_interior_bounded_boundary_order
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u v : Space n → ℝ}
    (hu : WeakPSubsolutionPair p Ω u (gradient u))
    (hv : WeakPSupersolutionPair p Ω v (gradient v))
    (huc : ContDiffOn ℝ 1 u Ω) (hvc : ContDiffOn ℝ 1 v Ω)
    (hucb : ContinuousOn u (closure Ω)) (hvcb : ContinuousOn v (closure Ω))
    (hn : 2≤n) (hΩb : Bornology.IsBounded Ω)
    (hboundary : ∀ x∈frontier Ω, u x≤v x) : ∀ x∈Ω, u x≤v x := by
  intro x hx
  by_contra hnot
  let ε : ℝ := (u x-v x)/2
  have hε : 0<ε := by dsimp only [ε]; linarith
  have hex : ε<u x-v x := by dsimp only [ε]; linarith
  let K : Set (Space n) := closure Ω ∩ {y | ε≤u y-v y}
  have hK : IsCompact K :=
    (hucb.sub hvcb).upperSemicontinuousOn.isCompact_inter_preimage_Ici hΩb.isCompact_closure ε
  have hKΩ : K ⊆ Ω := by
    intro y hy
    by_contra hyn
    have hyf : y∈frontier Ω := by
      rw [hu.2.1.frontier_eq]
      exact ⟨hy.1,hyn⟩
    have hb := hboundary y hyf
    have hd := hy.2
    change ε≤u y-v y at hd
    linarith
  have hxK : x∈K := ⟨subset_closure hx,hex.le⟩
  obtain ⟨δ,hδ,hδΩ⟩ := hK.exists_cthickening_subset_open hu.2.1 hKΩ
  let D : Set (Space n) := thickening δ K
  have hKD : K ⊆ D := self_subset_thickening hδ K
  have hD : LocalDomain D Ω :=
    ⟨isOpen_thickening,hK.isBounded.thickening,
      (closure_thickening_subset_cthickening δ K).trans hδΩ⟩
  let w : Space n → ℝ := fun y => v y+ε
  have hgw : gradient w=gradient v :=
    funext (fun y => BMCompactAnalytic.gradient_add_const v ε y)
  have hsuperw : WeakPSupersolutionPair p Ω w (gradient w) := by
    rw [hgw]
    exact hv.add_const ε
  have hwb : ∀ y∈frontier D, u y≤w y := by
    intro y hy
    have hyΩ : y∈Ω := hD.2.2 (frontier_subset_closure hy)
    have hynK : y∉K := by
      intro hyK
      have hyD := hKD hyK
      rw [hD.1.frontier_eq] at hy
      exact hy.2 hyD
    have hlt : u y-v y<ε := by
      by_contra hge
      exact hynK ⟨subset_closure hyΩ,le_of_not_gt hge⟩
    dsimp only [w]
    linarith
  have hle := hu.leOn_of_local_C1_boundary_order hsuperw huc
    (hvc.add contDiffOn_const) hn hD hwb x (hKD hxK)
  dsimp only [w,ε] at hle
  linarith

/-- Existential actual weak gradients are identified on the open interior;
continuity on the closure suffices for ordinary bounded-domain frontier order. -/
theorem IsWeakPHarmonic.leOn_of_C1_interior_bounded_boundary_order
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u v : Space n → ℝ}
    (hu : IsWeakPHarmonic p Ω u) (hv : IsWeakPHarmonic p Ω v)
    (huc : ContDiffOn ℝ 1 u Ω) (hvc : ContDiffOn ℝ 1 v Ω)
    (hucb : ContinuousOn u (closure Ω)) (hvcb : ContinuousOn v (closure Ω))
    (hn : 2≤n) (hΩb : Bornology.IsBounded Ω)
    (hboundary : ∀ x∈frontier Ω, u x≤v x) : ∀ x∈Ω, u x≤v x := by
  obtain ⟨g,hu⟩ := hu
  obtain ⟨h,hv⟩ := hv
  exact (hu.with_classical_gradient huc).subsolution.leOn_of_C1_interior_bounded_boundary_order
    (hv.with_classical_gradient hvc).supersolution huc hvc hucb hvcb hn hΩb hboundary

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSubsolutionPair.leOn_of_C1_interior_bounded_boundary_order
#print axioms BMCompactPDE.IsWeakPHarmonic.leOn_of_C1_interior_bounded_boundary_order
