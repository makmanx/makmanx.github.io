import FilledNeighborhoodTrace
import GreenComponentSign
import UpstreamGreenTranslation
import CriticalBallOuterCapacity

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Bornology
open scoped Topology
namespace BMCompactPDE

/-- The filled compact set is exactly the zero set of every actual normalized
exterior Green function, for both critical and supercritical exponents. -/
theorem IsExteriorGreen.fill_eq_zero_set {n : ℕ} {p σ : ℝ} {K : Set (Space n)} {G : Space n → ℝ}
    (hG : IsExteriorGreen n σ p K G) : fillBoundedHoles K = {x | G x = 0} := by
  ext x
  constructor
  · rintro (hx | ⟨hx,hb⟩)
    · exact hG.2.2.2.2.2.2.1 hx
    · exact (hG.sign_on_complement_component hx).1 hb
  · intro hx
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · refine Or.inr ⟨hxK,?_⟩
      by_contra hu
      exact (ne_of_gt ((hG.sign_on_complement_component hxK).2 hu)) hx

theorem IsExteriorGreen.isCompact_fill {n : ℕ} {p σ : ℝ} {K : Set (Space n)} {G : Space n → ℝ}
    (hG : IsExteriorGreen n σ p K G) : IsCompact (fillBoundedHoles K) := by
  rw [hG.fill_eq_zero_set]
  have hb : IsBounded {x : Space n | 0 < G x}ᶜ := isBounded_compl_iff.mpr
    (hG.tendsto_atTop_at_infinity.eventually (eventually_gt_atTop 0))
  exact (Metric.isCompact_iff_isClosed_bounded).mpr
    ⟨isClosed_eq hG.2.2.2.2.2.1 continuous_const,hb.subset (fun x hx => not_lt.mpr (le_of_eq hx))⟩

/-- Filling preserves the actual Green function and its normalization at infinity. -/
theorem IsExteriorGreen.on_filled {n : ℕ} {p σ : ℝ} {K : Set (Space n)} {G : Space n → ℝ}
    (hG : IsExteriorGreen n σ p K G) : IsExteriorGreen n σ p (fillBoundedHoles K) G := by
  have hcompact := hG.isCompact_fill
  have hzero := hG.fill_eq_zero_set
  obtain ⟨hn,hp,hσ,_,hne,hc,_,⟨g,hweak⟩,hrem⟩ := hG
  have hs : K ⊆ fillBoundedHoles K := subset_union_left
  refine ⟨hn,hp,hσ,hcompact,hne.mono hs,hc,?_,⟨g,
    hweak.mono (compl_subset_compl.mpr hs) hcompact.isClosed.isOpen_compl⟩,hrem⟩
  intro x hx
  rw [hzero] at hx
  exact hx

theorem isCompact_fillBoundedHoles_of_nonempty {n : ℕ} (hn : 2 ≤ n)
    {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty) : IsCompact (fillBoundedHoles K) := by
  obtain ⟨_,_,hG,_⟩ := exists_canonical_exterior_green_supercritical_nonempty
    (p := (n:ℝ)+1) hn (lt_add_one _) hK hne
  exact hG.isCompact_fill

theorem HasCriticalGreenCapacity.on_filled {n : ℕ} {σ c : ℝ} {K : Set (Space n)}
    (hc : HasCriticalGreenCapacity σ K c) : HasCriticalGreenCapacity σ (fillBoundedHoles K) c := by
  obtain ⟨G,k,hG,hk,he⟩ := hc
  exact ⟨G,k,hG.on_filled,hk,he⟩

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.fill_eq_zero_set
#print axioms BMCompactPDE.IsExteriorGreen.isCompact_fill
#print axioms BMCompactPDE.IsExteriorGreen.on_filled
#print axioms BMCompactPDE.isCompact_fillBoundedHoles_of_nonempty
#print axioms BMCompactPDE.HasCriticalGreenCapacity.on_filled
