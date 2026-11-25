import NextCriticalSelectedRelative
import NextCriticalRelativeTrace
import NextComparisonCriticalBarrier
import NextComparisonBallGeometry
import UpstreamBoundaryNeighborhoodGeometry

/-! Actual critical unit-trace condenser potentials inside a finite outer ball.
Interior tangent balls supply the fully constructed logarithmic barriers. In
particular positive closed neighborhoods need no p-regularity, trace, candidate,
comparison or barrier-family assumption. Outer-boundary continuity is separate.
All true variational/Sobolev/gradient/admissible data are retained. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1400000 in
theorem exists_critical_relative_capacity_unit_trace_of_interior_tangent_balls
    {n : ℕ} (hn : 2≤n) {K : Set (Space n)} (hK : IsCompact K) {R : ℝ}
    (hKR : K⊆ball (0 : Space n) R)
    (hballs : ∀ a∈K,∃ z : Space n,∃ r : ℝ,0<r ∧ closedBall z r⊆K ∧ dist a z=r) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      ContinuousOn u (ball 0 R) ∧ (∀ x∈K,u x=1) ∧ (∀ x∉ball 0 R,u x=0) ∧
      (∀ x,0≤u x ∧ u x≤1) ∧ ZeroBoundarySobolevPair (n:ℝ) (ball 0 R) u g ∧
      SobolevPair (n:ℝ) univ u g ∧ WeakPHarmonicPair (n:ℝ) (ball 0 R\K) u g ∧
      BMCompactCapacityV2.relativeCapacity (n:ℝ) K (ball 0 R)=
        ENNReal.ofReal (∫ x in ball 0 R,‖g x‖^(n:ℝ) ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K (ball 0 R) (φ j)) ∧
        Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal (n:ℝ)) volume) atTop (𝓝 0) ∧
        Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal (n:ℝ)) volume) atTop (𝓝 0) := by
  have hn0 : 0<n := lt_of_lt_of_le (by decide : 0<2) hn
  have hp : 1<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2) hn)
  obtain ⟨u,g,huc,huO,hub,huW,huS,huH,huB,hcap,φ,hφ,hlu,hlg⟩ :=
    exists_selected_unit_bounded_relative_capacity_potential_allp hp hn hK isOpen_ball hKR isBounded_ball
  have hluR : Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal (n:ℝ))
      (volume.restrict (ball (0 : Space n) R))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlu (fun _=>bot_le)
      (fun _=>eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hlgR : Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal (n:ℝ))
      (volume.restrict (ball (0 : Space n) R))) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlg (fun _=>bot_le)
      (fun _=>eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hbarrier (a : Space n) (ha : a∈K) : ∃ B : ℕ → Space n → ℝ,
      (∀ j,ContDiff ℝ ∞ (B j)) ∧ (∀ j x,x∈K → B j x≤1) ∧
      (∀ j,WeakPHarmonicPair (n:ℝ) (ball 0 R\K) (B j) (gradient (B j))) ∧
      (∀ j x,x∉ball 0 R → B j x≤0) ∧ Tendsto (fun j=>B j a) atTop (𝓝 1) := by
    obtain ⟨z,r,hr,hsub,har⟩ := hballs a ha
    have hsep := norm_add_radius_lt_of_closedBall_subset_ball_zero hn0 z hr (hsub.trans hKR)
    obtain ⟨B,hB,hB1,hBO,hBH,hBa⟩ := exists_smooth_critical_finite_ball_barrier_sequence hn z hr hsep har
    refine ⟨B,hB,(fun j x _=>hB1 j x),?_,hBO,hBa⟩
    intro j
    apply (hBH j).mono _ (isOpen_ball.sdiff hK.isClosed)
    intro x hx hxball
    exact hx.2 (hsub hxball)
  obtain ⟨v,hvc,hvu,hvK,hvout,-⟩ :=
    huH.exists_continuous_relative_unit_extension_of_smooth_barriers hK hn isOpen_ball hKR isBounded_ball
      huc (huS.mono_actual (subset_univ _)) (ae_restrict_of_ae huB) (fun x hx=>(hub x hx).2)
      hφ hluR hlgR hbarrier
  have hvO (x : Space n) (hx : x∉ball 0 R) : v x=0 := by
    have hxK : x∉K := fun hh=>hx (hKR hh)
    rw [hvout x hxK]
    exact huO x hx
  have hvb (x : Space n) : 0≤v x ∧ v x≤1 := by
    by_cases hxK : x∈K
    · rw [hvK x hxK]
      exact ⟨zero_le_one,le_rfl⟩
    · by_cases hxO : x∈ball (0 : Space n) R
      · rw [hvout x hxK]
        exact hub x ⟨hxO,hxK⟩
      · rw [hvO x hxO]
        exact ⟨le_rfl,zero_le_one⟩
  have hvW := huW.congr (ae_restrict_of_ae hvu.symm) EventuallyEq.rfl
  have hvS := huS.congr (by simpa only [Measure.restrict_univ] using hvu.symm) EventuallyEq.rfl
  have hvH := huH.congr_ae (ae_restrict_of_ae hvu.symm) EventuallyEq.rfl
  have hluV : Tendsto (fun j=>eLpNorm (φ j-v) (ENNReal.ofReal (n:ℝ)) volume) atTop (𝓝 0) := by
    have he (j : ℕ) : eLpNorm (φ j-v) (ENNReal.ofReal (n:ℝ)) volume=
        eLpNorm (φ j-u) (ENNReal.ofReal (n:ℝ)) volume := eLpNorm_congr_ae (EventuallyEq.rfl.sub hvu)
    simpa only [he] using hlu
  exact ⟨v,g,hvc,hvK,hvO,hvb,hvW,hvS,hvH,hcap,φ,hφ,hluV,hlg⟩

theorem exists_critical_relative_capacity_unit_trace_closedNeighborhood
    {n : ℕ} (hn : 2≤n) {K : Set (Space n)} (hK : IsCompact K) {δ R : ℝ}
    (hδ : 0<δ) (hKR : BMCompact.closedNeighborhood δ K⊆ball (0 : Space n) R) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      ContinuousOn u (ball 0 R) ∧ (∀ x∈(BMCompact.closedNeighborhood δ K),u x=1) ∧ (∀ x∉ball 0 R,u x=0) ∧
      (∀ x,0≤u x ∧ u x≤1) ∧ ZeroBoundarySobolevPair (n:ℝ) (ball 0 R) u g ∧
      SobolevPair (n:ℝ) univ u g ∧ WeakPHarmonicPair (n:ℝ) (ball 0 R\(BMCompact.closedNeighborhood δ K)) u g ∧
      BMCompactCapacityV2.relativeCapacity (n:ℝ) (BMCompact.closedNeighborhood δ K) (ball 0 R)=
        ENNReal.ofReal (∫ x in ball 0 R,‖g x‖^(n:ℝ) ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible (BMCompact.closedNeighborhood δ K) (ball 0 R) (φ j)) ∧
        Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal (n:ℝ)) volume) atTop (𝓝 0) ∧
        Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal (n:ℝ)) volume) atTop (𝓝 0) := by
  have hn0 : 0<n := lt_of_lt_of_le (by decide : 0<2) hn
  exact exists_critical_relative_capacity_unit_trace_of_interior_tangent_balls hn
    (BMCompact.isCompact_closedNeighborhood hK δ) hKR
    (closedNeighborhood_has_interior_tangent_balls hn0 hK hδ)

end BMCompactPDE
#print axioms BMCompactPDE.exists_critical_relative_capacity_unit_trace_of_interior_tangent_balls
#print axioms BMCompactPDE.exists_critical_relative_capacity_unit_trace_closedNeighborhood
