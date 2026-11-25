import GradientHessianNaturalLimit

/-! Actual local Sobolev regularity of the natural gradient on arbitrary open
domains, for p>=2,n>=2. A bounded collar supplies the genuine local Sobolev data
required by the bounded-domain endpoint. No global norm, solution family,
derivative field, or gradient regularity is an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- The actual constant-source weak PDE constructs L2 weak derivatives of all
components of its zero-parameter natural gradient on each relatively compact
open subdomain. The ambient domain may be unbounded. -/
theorem WeakPSourcePair.exists_local_naturalGradient_sobolev_rows
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hH : WeakPSourcePair p c Ω f gf) (hp : 2≤p) (hn : 2≤n)
    {D : Set (Space n)} (hD : LocalDomain D Ω) :
    ∃ H : Fin n → Space n → Space n,
      ∀ i, SobolevPair 2 D (fun x => naturalGradientMap p 0 (gf x) i) (H i) := by
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_cthickening_subset_open hH.2.1 hD.2.2
  let U : Set (Space n) := thickening δ (closure D)
  have hU : LocalDomain U Ω := by
    refine ⟨isOpen_thickening,hK.isBounded.thickening,?_⟩
    exact (closure_thickening_subset_cthickening δ (closure D)).trans hthick
  have hDU : LocalDomain D U :=
    ⟨hD.1,hD.2.1,self_subset_thickening hδ (closure D)⟩
  have hUΩ : U⊆Ω := subset_closure.trans hU.2.2
  have hHU := hH.mono_actual hUΩ hU.1
  have hfU := hH.2.2.1 U hU
  exact hHU.exists_local_naturalGradient_sobolev_rows_ge_two hfU hp hn hU.2.1 hDU

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.exists_local_naturalGradient_sobolev_rows
