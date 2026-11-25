import UpstreamBoundaryBarrierComparison
import SuperContinuousBatch

/-! Genuine exterior comparison from continuous boundary values and actual
asymptotic order. Compact strict superlevels localize to relatively compact
open exterior domains, where the proved weak comparison applies. No ready-made
exterior comparison or global W0 test is an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem WeakPHarmonicPair.leOn_compl_of_continuous_boundary_order_and_infinity_order
    {n : ℕ} {p : ℝ} {K : Set (Space n)} (hK : IsCompact K) (hn : 2≤n)
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Kᶜ u g) (hv : WeakPHarmonicPair p Kᶜ v h)
    (huc : Continuous u) (hvc : Continuous v)
    (hboundary : ∀ x∈K,u x≤v x)
    (hinfty : ∀ ε : ℝ,0<ε → ∀ᶠ x in cocompact (Space n),u x-v x<ε) :
    ∀ x∈Kᶜ,u x≤v x := by
  have heps (ε : ℝ) (hε : 0<ε) : ∀ x∈Kᶜ,u x≤v x+ε := by
    let E : Set (Space n) := {x | ε≤u x-v x}
    obtain ⟨T,hT,hET⟩ := mem_cocompact'.mp (hinfty ε hε)
    have hE : IsCompact E := hT.of_isClosed_subset
      (isClosed_le continuous_const (huc.sub hvc)) (by
        intro y hy
        apply hET
        change ¬u y-v y<ε
        exact not_lt.mpr hy)
    have hEK : E⊆Kᶜ := by
      intro y hy hyK
      have hb := hboundary y hyK
      change ε≤u y-v y at hy
      linarith only [hy,hb,hε]
    obtain ⟨δ,hδ,hthick⟩ := hE.exists_cthickening_subset_open hK.isClosed.isOpen_compl hEK
    let O : Set (Space n) := thickening δ E
    have hO : IsOpen O := isOpen_thickening
    have hOL : LocalDomain O Kᶜ := ⟨hO,hE.isBounded.thickening,
      (closure_thickening_subset_cthickening δ E).trans hthick⟩
    have hEO : E⊆O := self_subset_thickening hδ E
    have horder : ∀ y∈frontier O,u y≤(v y+ε) := by
      intro y hy
      have hyn : y∉O := (hO.frontier_eq ▸ hy).2
      have hyE : y∉E := fun he=>hyn (hEO he)
      have hs : u y-v y<ε := lt_of_not_ge hyE
      linarith only [hs]
    have hlocal := hu.subsolution.leOn_of_continuous_boundary_order
      (hv.add_const ε).supersolution huc.continuousOn (hvc.add continuous_const).continuousOn hn hOL horder
    intro x hx
    by_contra hnot
    have hxE : x∈E := by change ε≤u x-v x;linarith only [lt_of_not_ge hnot]
    exact hnot (hlocal x (hEO hxE))
  intro x hx
  by_contra hnot
  have hε : 0<(u x-v x)/2 := by linarith only [lt_of_not_ge hnot]
  have he := heps ((u x-v x)/2) hε x hx
  linarith only [he,lt_of_not_ge hnot]

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.leOn_compl_of_continuous_boundary_order_and_infinity_order
