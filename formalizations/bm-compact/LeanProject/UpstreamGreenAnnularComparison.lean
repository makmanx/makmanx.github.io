import UpstreamBoundaryExteriorComparison

/-! Bounded weak comparison with continuous boundary data, using only actual
LOCAL Sobolev/PDE membership. Compact strict superlevels avoid the boundary;
no C1, global Sobolev bound or supplied W0 comparison test is required. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem WeakPHarmonicPair.leOn_of_bounded_continuous_boundary_order
    {n : ℕ} {p : ℝ} {O : Set (Space n)} (hn : 2≤n) (hOb : Bornology.IsBounded O)
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p O u g) (hv : WeakPHarmonicPair p O v h)
    (huc : ContinuousOn u (closure O)) (hvc : ContinuousOn v (closure O))
    (hboundary : ∀ x∈frontier O,u x≤v x) : ∀ x∈O,u x≤v x := by
  have heps (ε : ℝ) (hε : 0<ε) : ∀ x∈O,u x≤v x+ε := by
    let E : Set (Space n) := closure O∩{x | ε≤u x-v x}
    have hE : IsCompact E := (huc.sub hvc).upperSemicontinuousOn.isCompact_inter_preimage_Ici
      hOb.isCompact_closure ε
    have hEO : E⊆O := by
      intro x hx
      by_contra hnot
      have hxf : x∈frontier O := by rw [hu.2.1.frontier_eq];exact ⟨hx.1,hnot⟩
      have hb := hboundary x hxf
      have he : ε≤u x-v x := hx.2
      linarith only [hb,he,hε]
    obtain ⟨δ,hδ,hthick⟩ := hE.exists_cthickening_subset_open hu.2.1 hEO
    let D : Set (Space n) := thickening δ E
    have hD : IsOpen D := isOpen_thickening
    have hDL : LocalDomain D O := ⟨hD,hE.isBounded.thickening,
      (closure_thickening_subset_cthickening δ E).trans hthick⟩
    have hED : E⊆D := self_subset_thickening hδ E
    have horder : ∀ y∈frontier D,u y≤v y+ε := by
      intro y hy
      have hyO : y∈O := hDL.2.2 (frontier_subset_closure hy)
      have hyD : y∉D := (hD.frontier_eq ▸ hy).2
      have hnot : ¬ε≤u y-v y := fun he=>hyD (hED ⟨subset_closure hyO,he⟩)
      linarith only [lt_of_not_ge hnot]
    have hlocal := hu.subsolution.leOn_of_continuous_boundary_order (hv.add_const ε).supersolution
      (huc.mono subset_closure) ((hvc.add continuousOn_const).mono subset_closure) hn hDL horder
    intro x hx
    by_contra hnot
    have hex : ε≤u x-v x := by linarith only [lt_of_not_ge hnot]
    have hxE : x∈E := ⟨subset_closure hx,hex⟩
    exact hnot (hlocal x (hED hxE))
  intro x hx
  by_contra hnot
  have hε : 0<(u x-v x)/2 := by linarith only [lt_of_not_ge hnot]
  have he := heps ((u x-v x)/2) hε x hx
  linarith only [he,lt_of_not_ge hnot]

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.leOn_of_bounded_continuous_boundary_order
