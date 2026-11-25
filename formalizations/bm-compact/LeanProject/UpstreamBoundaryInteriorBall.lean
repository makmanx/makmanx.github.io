import UpstreamBoundaryNeighborhoodGeometry
import UpstreamFundamentalBarrier

/-! Genuine geometric boundary regularity for actual constructed capacitary
potentials. Interior tangent balls supply actual radial smooth barrier families;
positive compact neighborhoods satisfy the geometry by an actual construction.
No p-regularity predicate, barrier family, boundary trace or comparison is input
to the final neighborhood theorem. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem exists_continuous_unit_variational_capacity_potential_of_interior_tangent_balls
    {n : ℕ} {p : ℝ} (hp : 1<p) (hpn : p<(n:ℝ)) {K : Set (Space n)} (hK : IsCompact K)
    (hball : ∀ a∈K,∃ z : Space n,∃ R : ℝ,0<R ∧ closedBall z R⊆K ∧ dist a z=R) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      Continuous u ∧ (∀ x∈K,u x=1) ∧
      MemLp u (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume ∧
      MemLp g (ENNReal.ofReal p) volume ∧
      (∀ D : Set (Space n),Bornology.IsBounded D → SobolevPair p D u g) ∧
      WeakPHarmonicPair p Kᶜ u g ∧ (∀ x,0≤u x ∧ u x≤1) ∧
      Tendsto u (cocompact (Space n)) (𝓝 0) ∧
      BMCompactCapacityV2.relativeCapacity p K univ=ENNReal.ofReal (∫ x,‖g x‖^p ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K univ (φ j)) ∧
        Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume) atTop (𝓝 0) ∧
        Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  apply exists_continuous_unit_variational_capacity_potential_of_smooth_barriers hp hpn hK
  intro a ha
  obtain ⟨z,R,hR,hsub,haR⟩ := hball a ha
  obtain ⟨B,hB,hB1,hBH,hBi,hBa⟩ := exists_smooth_exterior_ball_barrier_sequence hp hpn z hR haR
  refine ⟨B,hB,(fun j x _=>hB1 j x),?_,hBi,hBa⟩
  intro j
  apply (hBH j).mono _ hK.isClosed.isOpen_compl
  intro x hx hxball
  exact hx (hsub hxball)

theorem exists_continuous_unit_capacity_potential_closedNeighborhood
    {n : ℕ} {p : ℝ} (hp : 1<p) (hpn : p<(n:ℝ)) {K : Set (Space n)} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      Continuous u ∧ (∀ x∈(BMCompact.closedNeighborhood δ K),u x=1) ∧
      MemLp u (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume ∧
      MemLp g (ENNReal.ofReal p) volume ∧
      (∀ D : Set (Space n),Bornology.IsBounded D → SobolevPair p D u g) ∧
      WeakPHarmonicPair p (BMCompact.closedNeighborhood δ K)ᶜ u g ∧ (∀ x,0≤u x ∧ u x≤1) ∧
      Tendsto u (cocompact (Space n)) (𝓝 0) ∧
      BMCompactCapacityV2.relativeCapacity p (BMCompact.closedNeighborhood δ K) univ=ENNReal.ofReal (∫ x,‖g x‖^p ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible (BMCompact.closedNeighborhood δ K) univ (φ j)) ∧
        Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume) atTop (𝓝 0) ∧
        Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hn1 : 1<n := by exact_mod_cast (hp.trans hpn)
  exact exists_continuous_unit_variational_capacity_potential_of_interior_tangent_balls hp hpn
    (BMCompact.isCompact_closedNeighborhood hK δ)
    (closedNeighborhood_has_interior_tangent_balls (Nat.zero_lt_of_lt hn1) hK hδ)

end BMCompactPDE
#print axioms BMCompactPDE.exists_continuous_unit_variational_capacity_potential_of_interior_tangent_balls
#print axioms BMCompactPDE.exists_continuous_unit_capacity_potential_closedNeighborhood
