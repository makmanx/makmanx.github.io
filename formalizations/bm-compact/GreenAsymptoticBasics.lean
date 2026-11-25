import GreenDefs
import Mathlib.Analysis.Normed.Module.Basic

/-!
Bookkeeping for the concrete remainder in source eqn2.9--eqn2.10.
These results do not assert that a bounded remainder has a limit or that
Green functions are unique. Those are nonlinear PDE obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology

namespace BMCompactPDE

theorem HasGreenAsymptotic.boundedRemainder {n : ℕ} {σ p k : ℝ}
    {G : Space n → ℝ} (hk : HasGreenAsymptotic n σ p G k) :
    HasBoundedGreenRemainder n σ p G := by
  refine ⟨|k| + 1, by positivity, ?_⟩
  have he : ∀ᶠ x in cobounded (Space n),
      dist (G x - fundamentalPotential n σ p x) k < 1 :=
    (Metric.tendsto_nhds.1 hk) 1 zero_lt_one
  filter_upwards [he] with x hx
  have hdist : |(G x - fundamentalPotential n σ p x) - k| < 1 := by
    simpa only [Real.dist_eq] using hx
  obtain ⟨hl, hr⟩ := abs_lt.mp hdist
  apply abs_le.mpr
  constructor
  · linarith [neg_le_abs k]
  · linarith [le_abs_self k]

/-- This is uniqueness of a finite asymptotic constant for the same function,
not uniqueness of Green functions for a compact set. -/
theorem HasGreenAsymptotic.unique {n : ℕ} [NeBot (cobounded (Space n))]
    {σ p k l : ℝ} {G : Space n → ℝ}
    (hk : HasGreenAsymptotic n σ p G k)
    (hl : HasGreenAsymptotic n σ p G l) : k = l :=
  tendsto_nhds_unique hk hl

theorem HasGreenAsymptotic.unique_of_dimension {n : ℕ} (hn : 0 < n)
    {σ p k l : ℝ} {G : Space n → ℝ}
    (hk : HasGreenAsymptotic n σ p G k)
    (hl : HasGreenAsymptotic n σ p G l) : k = l := by
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact hk.unique hl

theorem HasBoundedGreenRemainder.congr_eventually {n : ℕ} {σ p : ℝ}
    {G H : Space n → ℝ} (hG : HasBoundedGreenRemainder n σ p G)
    (hGH : G =ᶠ[cobounded (Space n)] H) : HasBoundedGreenRemainder n σ p H := by
  obtain ⟨C, hC, hbound⟩ := hG
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, hGH] with x hx hxeq
  simpa only [← hxeq] using hx

theorem HasGreenAsymptotic.congr_eventually {n : ℕ} {σ p k : ℝ}
    {G H : Space n → ℝ} (hG : HasGreenAsymptotic n σ p G k)
    (hGH : G =ᶠ[cobounded (Space n)] H) : HasGreenAsymptotic n σ p H k := by
  apply hG.congr'
  filter_upwards [hGH] with x hx
  rw [hx]

end BMCompactPDE

#print axioms BMCompactPDE.HasGreenAsymptotic.boundedRemainder
#print axioms BMCompactPDE.HasGreenAsymptotic.unique
#print axioms BMCompactPDE.HasGreenAsymptotic.unique_of_dimension
#print axioms BMCompactPDE.HasBoundedGreenRemainder.congr_eventually
#print axioms BMCompactPDE.HasGreenAsymptotic.congr_eventually
