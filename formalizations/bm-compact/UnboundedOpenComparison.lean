import OuterNeighborhoodPotential
import UpstreamGreenAnnularComparison

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology
namespace BMCompactPDE

/-- Exterior comparison on an arbitrary open region, including half-spaces
with a compact obstacle removed. Boundary values and order at infinity
are required only on the closure of that region. -/
theorem WeakPHarmonicPair.le_of_frontier_and_decay {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    (hn : 2≤n) {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hv : WeakPHarmonicPair p Ω v h)
    (huc : Continuous u) (hvc : Continuous v) (hfr : ∀ x∈frontier Ω,u x≤v x)
    (hd : ∀ ε : ℝ, 0<ε → ∀ᶠ x in cocompact (Space n), u x-v x<ε) :
    ∀ x∈Ω,u x≤v x := by
  intro x hx
  by_contra! hbad
  let ε := (u x-v x)/2
  have hε : 0<ε := by dsimp [ε];linarith
  let E := {z | ε ≤ u z-v z} ∩ closure Ω
  obtain ⟨T,hT,hET⟩ := mem_cocompact'.mp (hd ε hε)
  have hE : IsCompact E := hT.of_isClosed_subset
    ((isClosed_le continuous_const (huc.sub hvc)).inter isClosed_closure)
    (fun y hy=> hET (show ¬ u y-v y<ε from not_lt.mpr (show ε≤u y-v y from hy.1)))
  have hsub : E ⊆ Ω := by
    intro z hz
    by_contra hzΩ
    have hfront : z∈frontier Ω := hu.2.1.frontier_eq ▸ ⟨hz.2,hzΩ⟩
    have h := hfr z hfront
    have hh : ε≤u z-v z := hz.1
    linarith
  obtain ⟨r,hr,hro⟩ := hE.exists_cthickening_subset_open hu.2.1 hsub
  let D := thickening r E
  have hD : LocalDomain D Ω := ⟨isOpen_thickening,hE.isBounded.thickening,
    (closure_thickening_subset_cthickening r E).trans hro⟩
  have hED := self_subset_thickening hr E
  have hb (y : Space n) (hy : y∈frontier D) : u y≤ v y+ε := by
    have hyD : y∉D := (hD.1.frontier_eq ▸ hy).2
    have hyΩ : y∈closure Ω := subset_closure (hD.2.2 (frontier_subset_closure hy))
    have hlt : u y-v y<ε := lt_of_not_ge fun h=>hyD (hED ⟨h,hyΩ⟩)
    linarith
  have hxE : x∈E := ⟨by change (u x - v x)/2 ≤ u x-v x;linarith,subset_closure hx⟩
  have hl := hu.subsolution.leOn_of_continuous_boundary_order (hv.add_const ε).supersolution
    huc.continuousOn (hvc.add continuous_const).continuousOn hn hD hb x (hED hxE)
  change u x≤v x + (u x-v x)/2 at hl
  linarith

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.le_of_frontier_and_decay
