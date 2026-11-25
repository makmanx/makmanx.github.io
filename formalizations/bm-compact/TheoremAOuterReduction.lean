import CapacityNeighborhood
import Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Actual outer-neighbourhood step in the proof of Theorem A(a), source
BM_Compact_Final.tex lines1627-1638. This is an explicit conditional reduction:
the Brunn--Minkowski inequality for the regular approximating neighbourhoods
is a hypothesis. Its nonlinear PDE proof is NOT supplied here.
-/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped ENNReal Pointwise Topology

namespace BMCompactCapacityV2

theorem subcriticalBM_of_neighborhood_BM {n : ℕ}
    (p : ℝ) (hp : 1 < p) (hpn : p < (n : ℝ))
    {E F : Set (Space n)} (hE : IsCompact E) (hF : IsCompact F)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (happrox : ∀ δ : ℝ, 0 < δ →
      ENNReal.ofReal t * variationalCapacity p (Metric.cthickening δ E) ^
          (1 / ((n : ℝ) - p)) +
        ENNReal.ofReal (1 - t) * variationalCapacity p (Metric.cthickening δ F) ^
          (1 / ((n : ℝ) - p)) ≤
      variationalCapacity p
        (t • Metric.cthickening δ E + (1 - t) • Metric.cthickening δ F) ^
          (1 / ((n : ℝ) - p))) :
    ENNReal.ofReal t * variationalCapacity p E ^ (1 / ((n : ℝ) - p)) +
      ENNReal.ofReal (1 - t) * variationalCapacity p F ^ (1 / ((n : ℝ) - p)) ≤
    variationalCapacity p (t • E + (1 - t) • F) ^ (1 / ((n : ℝ) - p)) := by
  have hq : 0 ≤ 1 / ((n : ℝ) - p) := (one_div_pos.mpr (sub_pos.mpr hpn)).le
  have hM : IsCompact (t • E + (1 - t) • F) := (hE.smul t).add (hF.smul (1 - t))
  have hlim := (tendsto_variationalCapacity_cthickening p
    (zero_lt_one.trans hp) hM).ennrpow_const (1 / ((n : ℝ) - p))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hEδ := ENNReal.rpow_le_rpow
    (variationalCapacity_mono p (Metric.self_subset_cthickening E (δ := δ))) hq
  have hFδ := ENNReal.rpow_le_rpow
    (variationalCapacity_mono p (Metric.self_subset_cthickening F (δ := δ))) hq
  have hmonE := mul_le_mul (le_refl (ENNReal.ofReal t)) hEδ zero_le zero_le
  have hmonF := mul_le_mul (le_refl (ENNReal.ofReal (1 - t))) hFδ zero_le zero_le
  have hmon := add_le_add hmonE hmonF
  have hgeom : t • Metric.cthickening δ E + (1 - t) • Metric.cthickening δ F =
      Metric.cthickening δ (t • E + (1 - t) • F) :=
    BMCompact.weighted_closedNeighborhood hE hF ht ht1 hδ.le
  exact hmon.trans (by simpa only [hgeom] using happrox δ hδ)

end BMCompactCapacityV2

#print axioms BMCompactCapacityV2.subcriticalBM_of_neighborhood_BM
