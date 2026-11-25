import GreenObstacleOrder
import UpstreamGreenAnnularComparison
import PropagationPrinciples
import Mathlib.Topology.Connected.LocallyConnected

/-! A normalized Green function is positive on every unbounded exterior
component and vanishes on each bounded component. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Bornology
open scoped Topology
namespace BMCompactPDE

theorem IsExteriorGreen.sign_on_complement_component
    {n : ℕ} {σ p : ℝ} {K : Set (Space n)} {u : Space n → ℝ}
    (hu : IsExteriorGreen n σ p K u) {a : Space n} (ha : a ∉ K) :
    (IsBounded (connectedComponentIn Kᶜ a) → u a = 0) ∧
      (¬ IsBounded (connectedComponentIn Kᶜ a) → 0 < u a) := by
  let D := connectedComponentIn Kᶜ a
  have hposInf := hu.tendsto_atTop_at_infinity.eventually (eventually_gt_atTop 0)
  have hnonneg := hu.nonnegative
  obtain ⟨hn,hp,_,hK,_,hc,h0,⟨g,hg⟩,_⟩ := hu
  have hnNat : 1 < n := by exact_mod_cast hn
  have hn2 : 2 ≤ n := by omega
  have hΩ := hK.isClosed.isOpen_compl
  have hD : IsOpen D := hΩ.connectedComponentIn
  have haD : a ∈ D := mem_connectedComponentIn ha
  have hgD := hg.mono (connectedComponentIn_subset Kᶜ a) hD
  constructor
  · intro hbounded
    have hfrontier : frontier D ⊆ K := by
      intro y hy
      by_contra hyK
      let E := connectedComponentIn Kᶜ y
      have hE : IsOpen E := hΩ.connectedComponentIn
      have hyE : y ∈ E := mem_connectedComponentIn hyK
      obtain ⟨z,hzE,hzD⟩ := mem_closure_iff.mp (frontier_subset_closure hy) E hE hyE
      have heq : D = E := (connectedComponentIn_eq hzD).trans (connectedComponentIn_eq hzE).symm
      exact (hD.frontier_eq ▸ hy).2 (by simpa only [heq] using hyE)
    have hzero := weakPHarmonicPair_const (hn.trans_le hp) hD 0
    have hcmp := hgD.leOn_of_bounded_continuous_boundary_order hn2 hbounded hzero
      hc.continuousOn continuousOn_const (fun y hy => (h0 (hfrontier hy)).le)
    exact le_antisymm (hcmp a haD) (hnonneg a)
  · intro hunbounded
    have hsome : ∃ x ∈ D, 0 < u x := by
      by_contra! hall
      have hb : IsBounded {x : Space n | 0 < u x}ᶜ := isBounded_compl_iff.mpr hposInf
      exact hunbounded (hb.subset (fun x hx => not_lt.mpr (hall x hx)))
    exact hgD.supersolution.positive_of_nonneg_of_positive_somewhere hn2 hc.continuousOn
      isPreconnected_connectedComponentIn (fun x _ => hnonneg x) hsome a haD

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.sign_on_complement_component
