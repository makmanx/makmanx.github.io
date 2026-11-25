import NextCriticalRelativeBarrier
import Mathlib.Topology.Piecewise

/-! An honest bounded-relative barrier criterion derives the inner unit trace.
The final patch preserves GLOBAL almost-everywhere equality because only K
inside O is changed. This is continuity on O, not yet at its outer boundary.
The geometric critical logarithmic family will discharge the explicit actual
barrier hypothesis in a separate constructed endpoint. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem nextCritical_trace_from_smooth_lower_barriers {n : ℕ}
    {D : Set (Space n)} {u : Space n → ℝ} {a : Space n}
    (hu1 : ∀ x∈D,u x≤1) {B : ℕ → Space n → ℝ}
    (hB : ∀ j,Continuous (B j)) (hBu : ∀ j x,x∈D → B j x≤u x)
    (hBa : Tendsto (fun j=>B j a) atTop (𝓝 1)) :
    Tendsto u (𝓝[D] a) (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j,hj⟩ := (hBa.eventually (eventually_gt_nhds (by linarith : 1-ε/2<(1:ℝ)))).exists
  have hnear : ∀ᶠ x in 𝓝[D] a,1-ε<B j x := by
    have ht := (hB j).continuousAt.tendsto.eventually (eventually_gt_nhds (by linarith only [hj,hε] : 1-ε<B j a))
    exact ht.filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear,eventually_mem_nhdsWithin] with x hx hxK
  have hlo := hBu j x hxK
  have hup := hu1 x hxK
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hup)]
  linarith only [hx,hlo]


set_option maxHeartbeats 1000000 in
theorem WeakPHarmonicPair.exists_continuous_relative_unit_extension_of_smooth_barriers
    {n : ℕ} {p : ℝ} {K O : Set (Space n)} (hK : IsCompact K) (hn : 2≤n)
    (hO : IsOpen O) (hKO : K⊆O) (hOb : Bornology.IsBounded O)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p (O\K) u g) (huc : ContinuousOn u (O\K))
    (hSob : SobolevPair p O u g) (hunit : ∀ᵐ x ∂volume.restrict O,0≤u x ∧ u x≤1)
    (hu1 : ∀ x∈O\K,u x≤1)
    {φ : ℕ → Space n → ℝ} (hφ : ∀ j,BMCompactCapacityV2.Admissible K O (φ j))
    (hlimu : Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0))
    (hlimg : Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0))
    (hbarrier : ∀ a∈K,∃ B : ℕ → Space n → ℝ,
      (∀ j,ContDiff ℝ ∞ (B j)) ∧ (∀ j x,x∈K → B j x≤1) ∧
      (∀ j,WeakPHarmonicPair p (O\K) (B j) (gradient (B j))) ∧
      (∀ j x,x∉O → B j x≤0) ∧ Tendsto (fun j=>B j a) atTop (𝓝 1)) :
    ∃ v : Space n → ℝ,ContinuousOn v O ∧ v=ᵐ[volume] u ∧
      (∀ x∈K,v x=1) ∧ (∀ x∉K,v x=u x) ∧
      ∀ a∈K,Tendsto u (𝓝[O\K] a) (𝓝 1) := by
  classical
  have hD : IsOpen (O\K) := hO.sdiff hK.isClosed
  have htrace (a : Space n) (ha : a∈K) : Tendsto u (𝓝[O\K] a) (𝓝 1) := by
    obtain ⟨B,hB,hBK,hBH,hBO,hBa⟩ := hbarrier a ha
    have hBu (j : ℕ) := hu.smooth_lower_barrier_le_on_bounded_relative_admissible_data
      hK hn hO hOb huc hSob (hunit.mono (fun _ hx=>hx.1)) hφ hlimu hlimg
      (hB j) (hBK j) (hBH j) (hBO j)
    exact nextCritical_trace_from_smooth_lower_barriers hu1 (fun j=>(hB j).continuous) hBu hBa
  let v : Space n → ℝ := fun x=>if x∈K then 1 else u x
  have hvK (x : Space n) (hx : x∈K) : v x=1 := if_pos hx
  have hvout (x : Space n) (hx : x∉K) : v x=u x := if_neg hx
  have hvc : ContinuousOn v O := by
    intro a haO
    by_cases ha : a∈K
    · change Tendsto v (𝓝[O] a) (𝓝 (v a))
      rw [hvK a ha]
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have ht := (Metric.tendsto_nhds.mp (htrace a ha)) ε hε
      have ht' : ∀ᶠ x in 𝓝 a,x∈O\K → dist (u x) 1<ε := eventually_nhdsWithin_iff.mp ht
      filter_upwards [ht'.filter_mono nhdsWithin_le_nhds,eventually_mem_nhdsWithin] with x hx hxO
      by_cases hxK : x∈K
      · rw [hvK x hxK,dist_self]
        exact hε
      · rw [hvout x hxK]
        exact hx ⟨hxO,hxK⟩
    · have heq : u=ᶠ[𝓝 a] v := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds ha] with x hx
        exact (hvout x hx).symm
      have hucAt : ContinuousAt u a := huc.continuousAt (hD.mem_nhds ⟨haO,ha⟩)
      have hvcAt : ContinuousAt v a := by
        change Tendsto v (𝓝 a) (𝓝 (v a))
        rw [hvout a ha]
        exact hucAt.congr' heq
      exact hvcAt.continuousWithinAt
  have hφm (j : ℕ) : AEStronglyMeasurable (φ j) (volume.restrict O) :=
    (hφ j).1.continuous.aestronglyMeasurable
  have hq0 : ENNReal.ofReal p≠0 := ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hu.1)
  have hm := tendstoInMeasure_of_tendsto_eLpNorm hq0 hφm hSob.2.1.1 hlimu
  obtain ⟨σ,-,hσ⟩ := hm.exists_seq_tendsto_ae
  have hσG : ∀ᵐ x ∂volume,x∈O → Tendsto (fun j=>φ (σ j) x) atTop (𝓝 (u x)) :=
    (ae_restrict_iff' hO.measurableSet).mp hσ
  have hunitG : ∀ᵐ x ∂volume,x∈O → 0≤u x ∧ u x≤1 :=
    (ae_restrict_iff' hO.measurableSet).mp hunit
  have hvae : v=ᵐ[volume] u := by
    filter_upwards [hσG,hunitG] with x hx hxunit
    by_cases hxK : x∈K
    · rw [hvK x hxK]
      have hxO : x∈O := hKO hxK
      have hlow : 1≤u x := ge_of_tendsto (hx hxO)
        (Eventually.of_forall (fun j=>(hφ (σ j)).2.2.2 x hxK))
      exact le_antisymm hlow (hxunit hxO).2
    · exact hvout x hxK
  exact ⟨v,hvc,hvae,hvK,hvout,htrace⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.exists_continuous_relative_unit_extension_of_smooth_barriers
