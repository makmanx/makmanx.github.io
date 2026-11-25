import OuterNeighborhoodPotential
import UpstreamGreenAnnularComparison
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Bornology
open scoped Topology ENNReal
namespace BMCompactPDE

/-- Fill a set by the bounded connected components of its complement. -/
def fillBoundedHoles {n : ℕ} (K : Set (Space n)) : Set (Space n) :=
  K ∪ {x | x ∈ Kᶜ ∧ IsBounded (connectedComponentIn Kᶜ x)}

theorem fillBoundedHoles_mono {n : ℕ} {K L : Set (Space n)} (h : K ⊆ L) :
    fillBoundedHoles K ⊆ fillBoundedHoles L := by
  intro x hx
  by_cases hxL : x ∈ L
  · exact Or.inl hxL
  · rcases hx with hxK | ⟨_,hb⟩
    · exact False.elim (hxL (h hxK))
    · exact Or.inr ⟨hxL,hb.subset (connectedComponentIn_mono _ (compl_subset_compl.mpr h))⟩

theorem ContinuousUnitCapacityData.unit_on_filled {n : ℕ} {p : ℝ} {K : Set (Space n)}
    (u : ContinuousUnitCapacityData p K) (hn : 2 ≤ n) (hp : 1 < p) (hK : IsCompact K) :
    ∀ x ∈ fillBoundedHoles K, u.scalar x = 1 := by
  intro x hx
  rcases hx with hxK | ⟨hxK,hb⟩
  · exact u.unit x hxK
  let D := connectedComponentIn Kᶜ x
  have ho := hK.isClosed.isOpen_compl
  have hD : IsOpen D := ho.connectedComponentIn
  have hfr : frontier D ⊆ K := by
    intro y hy
    by_contra hyK
    let E := connectedComponentIn Kᶜ y
    have hE : IsOpen E := ho.connectedComponentIn
    have hyE : y ∈ E := mem_connectedComponentIn hyK
    obtain ⟨z,hzE,hzD⟩ := mem_closure_iff.mp (frontier_subset_closure hy) E hE hyE
    have heq : D = E := (connectedComponentIn_eq hzD).trans (connectedComponentIn_eq hzE).symm
    exact (hD.frontier_eq ▸ hy).2 (heq ▸ hyE)
  have hconst := weakPHarmonicPair_const hp hD 1
  have hH := u.harmonic.mono (connectedComponentIn_subset Kᶜ x) hD
  have hge := hconst.leOn_of_bounded_continuous_boundary_order hn hb hH
    continuousOn_const u.continuous_scalar.continuousOn (fun y hy => (u.unit y (hfr hy)).ge)
  exact le_antisymm (u.bounds x).2 (hge x (mem_connectedComponentIn hxK))

/-- The upper-semicontinuous outer neighborhood potential is identically one
on the filled compactum, including every bounded complementary component. -/
theorem exists_outer_neighborhood_potential_unit_on_filled
    {n : ℕ} {p : ℝ} (hp : 1 < p) (hpn : p < (n:ℝ)) {K : Set (Space n)} (hK : IsCompact K) :
    ∃ U : (r : Ioi (0:ℝ)) → ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val K),
    ∃ v : Space n → ℝ, (∀ x, Monotone (fun r => (U r).scalar x)) ∧
      (∀ x, Tendsto (fun r => (U r).scalar x) atBot (𝓝 (v x))) ∧ UpperSemicontinuous v ∧
      (∀ x, 0 ≤ v x ∧ v x ≤ 1) ∧ (∀ x ∈ fillBoundedHoles K, v x = 1) ∧
      Tendsto v (cocompact (Space n)) (𝓝 0) := by
  classical
  let _ : Nonempty (Ioi (0:ℝ)) := ⟨⟨(1:ℝ),(by norm_num : (0:ℝ)<1)⟩⟩
  have hn1 : 1 < n := by exact_mod_cast hp.trans hpn
  obtain ⟨U,v,hm,hpnt,hsc,hb,_,hdec,_⟩ := exists_subcritical_outer_neighborhood_potential hp hpn hK
  refine ⟨U,v,hm,hpnt,hsc,hb,?_,hdec⟩
  intro x hx
  have he (r : Ioi (0:ℝ)) : (U r).scalar x = 1 :=
    (U r).unit_on_filled (by omega) hp (BMCompact.isCompact_closedNeighborhood hK r.val) x
      (fillBoundedHoles_mono (BMCompact.subset_closedNeighborhood K r.val) hx)
  exact tendsto_nhds_unique (hpnt x) (by simpa only [he] using
    (tendsto_const_nhds : Tendsto (fun _ : Ioi (0:ℝ) => (1:ℝ)) atBot (𝓝 1)))

end BMCompactPDE
#print axioms BMCompactPDE.fillBoundedHoles_mono
#print axioms BMCompactPDE.ContinuousUnitCapacityData.unit_on_filled
#print axioms BMCompactPDE.exists_outer_neighborhood_potential_unit_on_filled
