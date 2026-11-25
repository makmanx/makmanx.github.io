import CapacityOuterRegularity
import Mathlib.Topology.MetricSpace.Thickening

/-! Concrete outer continuity of the corrected smooth variational capacity on
compact sets, corresponding to the limit statement at manuscript label `lem9.2` / equation `eqn9.5`. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace BMCompactCapacityV2

theorem monotone_relativeCapacity_cthickening {n : ℕ} (p : ℝ)
    (K O : Set (Space n)) :
    Monotone (fun δ : ℝ => relativeCapacity p (Metric.cthickening δ K) O) := by
  intro δ ε hδε
  exact relativeCapacity_mono p (Metric.cthickening_mono hδε K)

theorem relativeCapacity_eq_iInf_cthickening {n : ℕ} (p : ℝ) (hp : 0 < p)
    {K : Set (Space n)} (hK : IsCompact K) (O : Set (Space n)) :
    relativeCapacity p K O =
      ⨅ (δ : ℝ) (_ : 0 < δ), relativeCapacity p (Metric.cthickening δ K) O := by
  apply le_antisymm
  · apply le_iInf
    intro δ
    apply le_iInf
    intro hδ
    exact relativeCapacity_mono p (Metric.self_subset_cthickening K)
  · rw [relativeCapacity_eq_openEnlargementInf p hp K O]
    apply le_iInf
    intro U
    apply le_iInf
    intro hU
    apply le_iInf
    intro hKU
    apply le_iInf
    intro hUO
    obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
    exact iInf_le_of_le δ (iInf_le_of_le hδ (relativeCapacity_mono p hδU))

theorem tendsto_relativeCapacity_cthickening {n : ℕ} (p : ℝ) (hp : 0 < p)
    {K : Set (Space n)} (hK : IsCompact K) (O : Set (Space n)) :
    Tendsto (fun δ : ℝ => relativeCapacity p (Metric.cthickening δ K) O)
      (𝓝[>] (0 : ℝ)) (𝓝 (relativeCapacity p K O)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall (fun δ =>
      ha.trans_le (relativeCapacity_mono p (Metric.self_subset_cthickening K)))
  · intro b hb
    have hinf : (⨅ (δ : ℝ) (_ : 0 < δ),
        relativeCapacity p (Metric.cthickening δ K) O) < b := by
      rwa [← relativeCapacity_eq_iInf_cthickening p hp hK O]
    simp only [iInf_lt_iff] at hinf
    obtain ⟨δ, hδ, hδb⟩ := hinf
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < δ :=
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
    filter_upwards [hev] with ε hεδ
    exact (relativeCapacity_mono p (Metric.cthickening_mono hεδ.le K)).trans_lt hδb

theorem tendsto_variationalCapacity_cthickening {n : ℕ} (p : ℝ) (hp : 0 < p)
    {K : Set (Space n)} (hK : IsCompact K) :
    Tendsto (fun δ : ℝ => variationalCapacity p (Metric.cthickening δ K))
      (𝓝[>] (0 : ℝ)) (𝓝 (variationalCapacity p K)) :=
  tendsto_relativeCapacity_cthickening p hp hK univ

end BMCompactCapacityV2

#print axioms BMCompactCapacityV2.relativeCapacity_eq_iInf_cthickening
#print axioms BMCompactCapacityV2.tendsto_relativeCapacity_cthickening
#print axioms BMCompactCapacityV2.tendsto_variationalCapacity_cthickening

#print axioms BMCompactCapacityV2.monotone_relativeCapacity_cthickening
