import FilledNeighborhoodTrace
import PropagationPrinciples
import WeakHarmonicScaling
import WeakAffine

noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology
namespace BMCompactPDE

private theorem frontier_comp_subset {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (a : Space n) :
    frontier (connectedComponentIn Kᶜ a) ⊆ K := by
  let D := connectedComponentIn Kᶜ a
  have ho := hK.isClosed.isOpen_compl
  have hD : IsOpen D := ho.connectedComponentIn
  intro y hy
  by_contra hyK
  let E := connectedComponentIn Kᶜ y
  have hE : IsOpen E := ho.connectedComponentIn
  have hyE : y ∈ E := mem_connectedComponentIn hyK
  obtain ⟨z,hzE,hzD⟩ := mem_closure_iff.mp (frontier_subset_closure hy) E hE hyE
  have heq : D = E := (connectedComponentIn_eq hzD).trans (connectedComponentIn_eq hzE).symm
  exact (hD.frontier_eq ▸ hy).2 (heq ▸ hyE)

theorem ContinuousUnitCapacityData.pos_of_nonempty {n : ℕ} {p : ℝ} {K : Set (Space n)}
    (u : ContinuousUnitCapacityData p K) (hn : 2 ≤ n) (hK : IsCompact K) (hne : K.Nonempty) (x : Space n) :
    0 < u.scalar x := by
  by_cases hx : x ∈ K
  · rw [u.unit x hx]; norm_num
  let D := connectedComponentIn Kᶜ x
  have hxD : x ∈ D := mem_connectedComponentIn hx
  have hsub : D ⊆ Kᶜ := connectedComponentIn_subset Kᶜ x
  have hnot : D ≠ univ := by
    intro h
    obtain ⟨y,hy⟩ := hne
    exact (hsub (h ▸ mem_univ y)) hy
  obtain ⟨b,hb⟩ := nonempty_frontier_iff.mpr ⟨⟨x,hxD⟩,hnot⟩
  have hone : u.scalar b = 1 := u.unit b (frontier_comp_subset hK x hb)
  have hsome : ∃ y ∈ D, 0 < u.scalar y := by
    by_contra! hall
    have he : EqOn u.scalar (fun _ => (0:ℝ)) D := fun y hy => le_antisymm (hall y hy) (u.bounds y).1
    have he' := he.closure u.continuous_scalar continuous_const (frontier_subset_closure hb)
    change u.scalar b = 0 at he'
    linarith
  have hH := u.harmonic.mono hsub hK.isClosed.isOpen_compl.connectedComponentIn
  exact hH.supersolution.positive_of_nonneg_of_positive_somewhere hn u.continuous_scalar.continuousOn
    isPreconnected_connectedComponentIn (fun y _ => (u.bounds y).1) hsome x hxD

theorem ContinuousUnitCapacityData.eq_one_iff_mem_fill {n : ℕ} {p : ℝ} {K : Set (Space n)}
    (u : ContinuousUnitCapacityData p K) (hn : 2 ≤ n) (hp : 1 < p) (hK : IsCompact K) (x : Space n) :
    u.scalar x = 1 ↔ x ∈ fillBoundedHoles K := by
  refine ⟨?_,u.unit_on_filled hn hp hK x⟩
  intro hone
  by_contra hx
  have hxK : x ∉ K := fun h => hx (Or.inl h)
  let D := connectedComponentIn Kᶜ x
  have hun : ¬ IsBounded D := fun hb => hx (Or.inr ⟨hxK,hb⟩)
  have hsmall : ∀ᶠ y in cobounded (Space n), u.scalar y < 1 := by
    simpa only [Metric.cobounded_eq_cocompact] using u.decay.eventually_lt_const zero_lt_one
  have hsome : ∃ y ∈ D, 0 < 1-u.scalar y := by
    by_contra! hall
    have hB : IsBounded {y : Space n | u.scalar y < 1}ᶜ := isBounded_compl_iff.mpr hsmall
    apply hun (hB.subset ?_)
    intro y hy
    change ¬ u.scalar y < 1
    exact not_lt.mpr (sub_nonpos.mp (hall y hy))
  have hH := u.harmonic.mono (connectedComponentIn_subset Kᶜ x) hK.isClosed.isOpen_compl.connectedComponentIn
  have hA := (hH.smul (-1)).add_const 1
  have he : EqOn (fun y => ((-1:ℝ) • u.scalar) y + 1) (fun y => 1-u.scalar y) D := by
    intro y _; simp [sub_eq_add_neg,add_comm]
  have hh := (hA.congr_fun he).supersolution.positive_of_nonneg_of_positive_somewhere hn
    (continuous_const.sub u.continuous_scalar).continuousOn isPreconnected_connectedComponentIn
    (fun y _ => sub_nonneg.mpr (u.bounds y).2) hsome x (mem_connectedComponentIn hxK)
  linarith

end BMCompactPDE
#print axioms BMCompactPDE.ContinuousUnitCapacityData.pos_of_nonempty
#print axioms BMCompactPDE.ContinuousUnitCapacityData.eq_one_iff_mem_fill
