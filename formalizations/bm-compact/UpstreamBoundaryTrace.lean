import UpstreamBoundaryBarrierComparison
import Mathlib.Topology.Piecewise

/-! Honest analytic barrier criterion for the selected capacity boundary trace.
Every barrier is an actual globally smooth function with the actual exterior
weak PDE, unit obstacle upper bound and zero infinity limit. Comparison is
proved from admissible approximation, not included in the criterion. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem upstream_trace_from_smooth_lower_barriers {n : ℕ}
    {K : Set (Space n)} {u : Space n → ℝ} {a : Space n}
    (hu1 : ∀ x∈Kᶜ,u x≤1) {B : ℕ → Space n → ℝ}
    (hB : ∀ j,Continuous (B j)) (hBu : ∀ j x,x∈Kᶜ → B j x≤u x)
    (hBa : Tendsto (fun j=>B j a) atTop (𝓝 1)) :
    Tendsto u (𝓝[Kᶜ] a) (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j,hj⟩ := (hBa.eventually (eventually_gt_nhds (by linarith : 1-ε/2<(1:ℝ)))).exists
  have hnear : ∀ᶠ x in 𝓝[Kᶜ] a,1-ε<B j x := by
    have ht := (hB j).continuousAt.tendsto.eventually (eventually_gt_nhds (by linarith only [hj,hε] : 1-ε<B j a))
    exact ht.filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear,eventually_mem_nhdsWithin] with x hx hxK
  have hlo := hBu j x hxK
  have hup := hu1 x hxK
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hup)]
  linarith only [hx,hlo]

set_option maxHeartbeats 600000 in
theorem WeakPHarmonicPair.exists_continuous_unit_extension_of_smooth_barriers
    {n : ℕ} {p q : ℝ} {K : Set (Space n)} (hK : IsCompact K) (hn : 2≤n)
    (hpq : p≤q) {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Kᶜ u g) (huc : ContinuousOn u Kᶜ)
    (hSob : ∀ O : Set (Space n),Bornology.IsBounded O → SobolevPair p O u g)
    (huq : MemLp u (ENNReal.ofReal q) volume)
    (hunit : ∀ᵐ x ∂volume,0≤u x ∧ u x≤1) (hu1 : ∀ x∈Kᶜ,u x≤1)
    {φ : ℕ → Space n → ℝ} (hφ : ∀ j,BMCompactCapacityV2.Admissible K univ (φ j))
    (hlimu : Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal q) volume) atTop (𝓝 0))
    (hlimg : Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0))
    (hbarrier : ∀ a∈K,∃ B : ℕ → Space n → ℝ,
      (∀ j,ContDiff ℝ ∞ (B j)) ∧ (∀ j x,x∈K → B j x≤1) ∧
      (∀ j,WeakPHarmonicPair p Kᶜ (B j) (gradient (B j))) ∧
      (∀ j,Tendsto (B j) (cocompact (Space n)) (𝓝 0)) ∧
      Tendsto (fun j=>B j a) atTop (𝓝 1)) :
    ∃ v : Space n → ℝ,Continuous v ∧ v=ᵐ[volume] u ∧
      (∀ x∈K,v x=1) ∧ (∀ x∈Kᶜ,v x=u x) ∧
      ∀ a∈K,Tendsto u (𝓝[Kᶜ] a) (𝓝 1) := by
  classical
  have htrace (a : Space n) (ha : a∈K) : Tendsto u (𝓝[Kᶜ] a) (𝓝 1) := by
    obtain ⟨B,hB,hBK,hBH,hBi,hBa⟩ := hbarrier a ha
    have hBu (j : ℕ) := hu.smooth_lower_barrier_le_of_admissible_approximation hK hn hpq
      huc hSob huq (hunit.mono (fun _ hx=>hx.1)) hφ hlimu hlimg (hB j) (hBK j) (hBH j) (hBi j)
    exact upstream_trace_from_smooth_lower_barriers hu1 (fun j=>(hB j).continuous) hBu hBa
  let v : Space n → ℝ := fun x=>if x∈K then 1 else u x
  have hvK (x : Space n) (hx : x∈K) : v x=1 := if_pos hx
  have hvout (x : Space n) (hx : x∈Kᶜ) : v x=u x := if_neg hx
  have hvc : Continuous v := by
    apply continuous_iff_continuousAt.mpr
    intro a
    by_cases ha : a∈K
    · change Tendsto v (𝓝 a) (𝓝 (v a))
      rw [hvK a ha]
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have ht := (Metric.tendsto_nhds.mp (htrace a ha)) ε hε
      have ht' : ∀ᶠ x in 𝓝 a,x∈Kᶜ → dist (u x) 1<ε := eventually_nhdsWithin_iff.mp ht
      filter_upwards [ht'] with x hx
      by_cases hxK : x∈K
      · rw [hvK x hxK,dist_self]
        exact hε
      · rw [hvout x hxK]
        exact hx hxK
    · have heq : u=ᶠ[𝓝 a] v := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds ha] with x hx
        exact (hvout x hx).symm
      change Tendsto v (𝓝 a) (𝓝 (v a))
      rw [hvout a ha]
      exact (huc.continuousAt (hK.isClosed.isOpen_compl.mem_nhds ha)).congr' heq
  have hφm (j : ℕ) : AEStronglyMeasurable (φ j) volume := (hφ j).1.continuous.aestronglyMeasurable
  have hq0 : ENNReal.ofReal q≠0 := ENNReal.ofReal_ne_zero_iff.mpr ((zero_lt_one.trans hu.1).trans_le hpq)
  have hm := tendstoInMeasure_of_tendsto_eLpNorm hq0 hφm huq.1 hlimu
  obtain ⟨σ,-,hσ⟩ := hm.exists_seq_tendsto_ae
  have hvae : v=ᵐ[volume] u := by
    filter_upwards [hσ,hunit] with x hx hxunit
    by_cases hxK : x∈K
    · rw [hvK x hxK]
      have hlow : 1≤u x := ge_of_tendsto hx (Eventually.of_forall (fun j=>(hφ (σ j)).2.2.2 x hxK))
      exact le_antisymm hlow hxunit.2
    · exact hvout x hxK
  exact ⟨v,hvc,hvae,hvK,hvout,htrace⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.exists_continuous_unit_extension_of_smooth_barriers
