import NextCriticalUpperComparison

/-! Actual outer zero-trace continuity from genuine nonnegative smooth weak
supersolutions. Their comparison is proved from the original actual W0 data,
not assumed. The interior selected representative and actual zero extension
are retained unchanged; global boundary continuity is the conclusion. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1200000 in
theorem WeakPHarmonicPair.continuous_zero_extension_of_smooth_outer_barriers
    {n : ℕ} {p : ℝ} {K O : Set (Space n)} (hK : IsCompact K) (hn : 2≤n)
    (hO : IsOpen O) (hKO : K⊆O) (hOb : Bornology.IsBounded O)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p (O\K) u g) (huc : ContinuousOn u O)
    (huW : ZeroBoundarySobolevPair p O u g)
    (huOut : ∀ x∉O,u x=0) (hunit : ∀ x,0≤u x ∧ u x≤1)
    (hbarrier : ∀ a∈frontier O,∃ B : ℕ → Space n → ℝ,
      (∀ j,ContDiff ℝ ∞ (B j)) ∧ (∀ j x,0≤B j x) ∧
      (∀ j x,x∈K → 1≤B j x) ∧
      (∀ j,WeakPHarmonicPair p (O\K) (B j) (gradient (B j))) ∧
      Tendsto (fun j=>B j a) atTop (𝓝 0)) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro a
  by_cases haO : a∈O
  · exact huc.continuousAt (hO.mem_nhds haO)
  · by_cases haCl : a∈closure O
    · have haF : a∈frontier O := by rw [hO.frontier_eq];exact ⟨haCl,haO⟩
      obtain ⟨B,hB,hB0,hBK,hBH,hBa⟩ := hbarrier a haF
      have hBu (j : ℕ) : ∀ x,u x≤B j x := by
        have hcmp := hu.smooth_upper_barrier_ge_of_actual_zeroBoundary_data hK hn hO hKO hOb
          (huc.mono sdiff_subset) huW (Eventually.of_forall (fun x=>(hunit x).2))
          (hB j) (hBK j) (fun x _=>hB0 j x) (hBH j)
        intro x
        by_cases hxO : x∈O
        · by_cases hxK : x∈K
          · exact (hunit x).2.trans (hBK j x hxK)
          · exact hcmp x ⟨hxO,hxK⟩
        · rw [huOut x hxO]
          exact hB0 j x
      change Tendsto u (𝓝 a) (𝓝 (u a))
      rw [huOut a haO]
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      obtain ⟨j,hj⟩ := (hBa.eventually (eventually_lt_nhds (half_pos hε))).exists
      have hnear := (hB j).continuous.continuousAt.tendsto.eventually
        (eventually_lt_nhds (hj.trans (half_lt_self hε)))
      filter_upwards [hnear] with x hx
      rw [Real.dist_eq,sub_zero,abs_of_nonneg (hunit x).1]
      exact (hBu j x).trans_lt hx
    · have heq : (fun _ : Space n=>(0:ℝ))=ᶠ[𝓝 a] u := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds haCl] with x hx
        exact (huOut x (fun hxO=>hx (subset_closure hxO))).symm
      change Tendsto u (𝓝 a) (𝓝 (u a))
      rw [huOut a haO]
      exact tendsto_const_nhds.congr' heq

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.continuous_zero_extension_of_smooth_outer_barriers
