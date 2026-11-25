import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
Exact geometric portions of BM_Compact_Final.tex, Lemma 4.9 (label `lem9.1`) (label lem9.1).
The ambient proper real normed vector space includes every finite-dimensional
Euclidean space in the manuscript. No capacity functional is assumed here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric
open scoped Pointwise

namespace BMCompact

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]

/-- The manuscript's closed δ-neighbourhood for nonnegative δ. -/
def closedNeighborhood (δ : ℝ) (E : Set V) : Set V := Metric.cthickening δ E

/-- Connect the encoding to the manuscript's distance-based definition. -/
theorem mem_closedNeighborhood_iff {E : Set V} (hE : E.Nonempty)
    {δ : ℝ} (hδ : 0 ≤ δ) (x : V) :
    x ∈ closedNeighborhood δ E ↔ Metric.infDist x E ≤ δ := by
  exact ENNReal.le_ofReal_iff_toReal_le (Metric.infEDist_ne_top hE) hδ

/-- Lemma 4.9 (label `lem9.1`)(a): a closed neighbourhood is a Minkowski sum with a closed ball. -/
theorem closedNeighborhood_eq_add_closedBall {E : Set V} (hE : IsCompact E)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    closedNeighborhood δ E = E + closedBall (0 : V) δ := by
  exact (hE.add_closedBall_zero hδ).symm

/-- Lemma 4.9 (label `lem9.1`)(a): closed neighbourhoods of compact sets are compact. -/
theorem isCompact_closedNeighborhood {E : Set V} (hE : IsCompact E) (δ : ℝ) :
    IsCompact (closedNeighborhood δ E) := hE.cthickening

/-- Lemma 4.9 (label `lem9.1`)(c), first inclusion. -/
theorem subset_closedNeighborhood (E : Set V) (δ : ℝ) :
    E ⊆ closedNeighborhood δ E := Metric.self_subset_cthickening E

/-- Lemma 4.9 (label `lem9.1`)(c), monotonicity in the neighbourhood radius. -/
theorem closedNeighborhood_mono (E : Set V) {δ' δ : ℝ} (h : δ' ≤ δ) :
    closedNeighborhood δ' E ⊆ closedNeighborhood δ E := Metric.cthickening_mono h E

/-- Lemma 4.9 (label `lem9.1`)(c), intersection identity, for closed sets (hence compact sets). -/
theorem iInter_closedNeighborhood {E : Set V} (hE : IsClosed E) :
    (⋂ (δ : ℝ) (_ : 0 < δ), closedNeighborhood δ E) = E := by
  simpa only [closedNeighborhood, hE.closure_eq] using
    (Metric.closure_eq_iInter_cthickening E).symm

/-- Lemma 4.9 (label `lem9.1`)(d), with an explicit positive threshold and all smaller radii. -/
theorem eventually_closedNeighborhood_subset_open {E O : Set V} (hE : IsCompact E)
    (hO : IsOpen O) (hEO : E ⊆ O) :
    ∃ ε > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ ≤ ε → closedNeighborhood δ E ⊆ O := by
  obtain ⟨ε, hε, hεO⟩ := hE.exists_cthickening_subset_open hO hEO
  exact ⟨ε, hε, fun δ _ hδε => (Metric.cthickening_mono hδε E).trans hεO⟩

/-- Ball identity used in Lemma 4.9 (label `lem9.1`)(b), including t=0 and t=1. -/
theorem weighted_closedBall {t δ : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hδ : 0 ≤ δ) :
    t • closedBall (0 : V) δ + (1 - t) • closedBall (0 : V) δ =
      closedBall (0 : V) δ := by
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  rw [smul_closedBall t 0 hδ, smul_closedBall (1 - t) 0 hδ]
  simp only [smul_zero, Real.norm_of_nonneg ht, Real.norm_of_nonneg h1t]
  rw [closedBall_add_closedBall (mul_nonneg ht hδ) (mul_nonneg h1t hδ)]
  congr 1
  · simp
  · ring

/-- Lemma 4.9 (label `lem9.1`)(b), weighted Minkowski combinations commute with equal-radius
closed neighbourhoods. -/
theorem weighted_closedNeighborhood {E F : Set V} (hE : IsCompact E) (hF : IsCompact F)
    {t δ : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hδ : 0 ≤ δ) :
    t • closedNeighborhood δ E + (1 - t) • closedNeighborhood δ F =
      closedNeighborhood δ (t • E + (1 - t) • F) := by
  rw [closedNeighborhood_eq_add_closedBall hE hδ,
    closedNeighborhood_eq_add_closedBall hF hδ,
    closedNeighborhood_eq_add_closedBall ((hE.smul t).add (hF.smul (1 - t))) hδ]
  rw [smul_add, smul_add, add_add_add_comm, weighted_closedBall ht ht1 hδ]

/-- Lemma 4.9 (label `lem9.1`)(b), translation/dilation formula, written using singleton addition. -/
theorem affine_closedNeighborhood {E : Set V} (hE : IsCompact E)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ) (x : V) :
    closedNeighborhood δ (ρ • E + {x}) =
      ρ • closedNeighborhood (δ / ρ) E + {x} := by
  rw [closedNeighborhood_eq_add_closedBall ((hE.smul ρ).add isCompact_singleton) hδ,
    closedNeighborhood_eq_add_closedBall hE (div_nonneg hδ hρ.le), smul_add]
  have hball : ρ • closedBall (0 : V) (δ / ρ) = closedBall (0 : V) δ := by
    rw [smul_closedBall ρ 0 (div_nonneg hδ hρ.le)]
    simp only [smul_zero, Real.norm_of_nonneg hρ.le]
    congr 1
    field_simp
  rw [hball]
  ac_rfl

#print axioms mem_closedNeighborhood_iff
#print axioms closedNeighborhood_eq_add_closedBall
#print axioms isCompact_closedNeighborhood
#print axioms subset_closedNeighborhood
#print axioms closedNeighborhood_mono
#print axioms iInter_closedNeighborhood
#print axioms eventually_closedNeighborhood_subset_open
#print axioms weighted_closedBall
#print axioms weighted_closedNeighborhood
#print axioms affine_closedNeighborhood

end BMCompact
