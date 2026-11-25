import NextCriticalInteriorTrace
import NextCriticalOuterTrace
import NextComparisonCriticalUpperBarrier
import NextComparisonOuterGeometry

/-! Genuine critical globally continuous unit relative capacitary potentials.
Actual inner logarithmic barriers and actual outer tangent-ball supersolutions
supply both traces from true variational/W0 data. Positive closed neighborhoods
need no p-regularity, barrier, trace, candidate or regularity premise. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1200000 in
theorem exists_continuous_unit_critical_relative_capacity_potential_of_interior_tangent_balls
    {n : ℕ} (hn : 2≤n) {K : Set (Space n)} (hK : IsCompact K) {R : ℝ} (hR : 0<R)
    (hKR : K⊆ball (0 : Space n) R)
    (hballs : ∀ a∈K,∃ z : Space n,∃ r : ℝ,0<r ∧ closedBall z r⊆K ∧ dist a z=r) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      Continuous u ∧ (∀ x∈K,u x=1) ∧ (∀ x∉ball 0 R,u x=0) ∧
      (∀ x,0≤u x ∧ u x≤1) ∧ ZeroBoundarySobolevPair (n:ℝ) (ball 0 R) u g ∧
      SobolevPair (n:ℝ) univ u g ∧ WeakPHarmonicPair (n:ℝ) (ball 0 R\K) u g ∧
      BMCompactCapacityV2.relativeCapacity (n:ℝ) K (ball 0 R)=
        ENNReal.ofReal (∫ x in ball 0 R,‖g x‖^(n:ℝ) ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K (ball 0 R) (φ j)) ∧
        Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal (n:ℝ)) volume) atTop (𝓝 0) ∧
        Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal (n:ℝ)) volume) atTop (𝓝 0) := by
  obtain ⟨u,g,huc,huK,huOut,hB,huW,huS,huH,hcap,φ,hφ,hLu,hLg⟩ :=
    exists_critical_relative_capacity_unit_trace_of_interior_tangent_balls hn hK hKR hballs
  have hbarrier (a : Space n) (ha : a∈frontier (ball (0 : Space n) R)) : ∃ B : ℕ → Space n → ℝ,
      (∀ j,ContDiff ℝ ∞ (B j)) ∧ (∀ j x,0≤B j x) ∧ (∀ j x,x∈K → 1≤B j x) ∧
      (∀ j,WeakPHarmonicPair (n:ℝ) (ball 0 R\K) (B j) (gradient (B j))) ∧
      Tendsto (fun j=>B j a) atTop (𝓝 0) := by
    have hanorm : ‖a‖=R := by
      simpa only [mem_sphere,dist_zero_right] using (frontier_ball_subset_sphere ha)
    obtain ⟨z,r,L,hr,hrL,har,hOext,hKL⟩ :=
      exists_outer_sphere_tangent_ball_separated_from_compact hK hR hKR hanorm
    obtain ⟨B,hBc,hB0,hBL,hBH,hBa⟩ :=
      exists_smooth_critical_exterior_tangent_upper_barrier_sequence hn z hr hrL har
    refine ⟨B,hBc,hB0,(fun j x hx=>hBL j x (hKL x hx)),?_,hBa⟩
    intro j
    apply (hBH j).mono _ (isOpen_ball.sdiff hK.isClosed)
    intro x hx
    exact hOext hx.1
  have hc := huH.continuous_zero_extension_of_smooth_outer_barriers hK hn isOpen_ball hKR isBounded_ball
    huc huW huOut hB hbarrier
  exact ⟨u,g,hc,huK,huOut,hB,huW,huS,huH,hcap,φ,hφ,hLu,hLg⟩

theorem exists_continuous_unit_critical_relative_capacity_potential_closedNeighborhood
    {n : ℕ} (hn : 2≤n) {K : Set (Space n)} (hK : IsCompact K) {δ R : ℝ}
    (hδ : 0<δ) (hR : 0<R) (hKR : BMCompact.closedNeighborhood δ K⊆ball (0 : Space n) R) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      Continuous u ∧ (∀ x∈(BMCompact.closedNeighborhood δ K),u x=1) ∧ (∀ x∉ball 0 R,u x=0) ∧
      (∀ x,0≤u x ∧ u x≤1) ∧ ZeroBoundarySobolevPair (n:ℝ) (ball 0 R) u g ∧
      SobolevPair (n:ℝ) univ u g ∧ WeakPHarmonicPair (n:ℝ) (ball 0 R\(BMCompact.closedNeighborhood δ K)) u g ∧
      BMCompactCapacityV2.relativeCapacity (n:ℝ) (BMCompact.closedNeighborhood δ K) (ball 0 R)=
        ENNReal.ofReal (∫ x in ball 0 R,‖g x‖^(n:ℝ) ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible (BMCompact.closedNeighborhood δ K) (ball 0 R) (φ j)) ∧
        Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal (n:ℝ)) volume) atTop (𝓝 0) ∧
        Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal (n:ℝ)) volume) atTop (𝓝 0) := by
  have hn0 : 0<n := lt_of_lt_of_le (by decide : 0<2) hn
  exact exists_continuous_unit_critical_relative_capacity_potential_of_interior_tangent_balls hn
    (BMCompact.isCompact_closedNeighborhood hK δ) hR hKR
    (closedNeighborhood_has_interior_tangent_balls hn0 hK hδ)

end BMCompactPDE
#print axioms BMCompactPDE.exists_continuous_unit_critical_relative_capacity_potential_of_interior_tangent_balls
#print axioms BMCompactPDE.exists_continuous_unit_critical_relative_capacity_potential_closedNeighborhood
