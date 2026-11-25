import ExteriorCapacityConstruction
import CapacityNeighborhood
import Geometry
import Mathlib.Topology.Order.AtTopBotIxx

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace BMCompactPDE

variable {n : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]

private theorem admissible_graph_antitone {K L : Set (Space n)} (h : K ⊆ L) :
    exteriorCapacityClass p q L ⊆ exteriorCapacityClass p q K := by
  apply closure_mono
  rintro w ⟨φ,hφ,hu,hg⟩
  exact ⟨φ,⟨hφ.1,hφ.2.1,hφ.2.2.1,fun x hx => hφ.2.2.2 x (h hx)⟩,hu,hg⟩

/-- In the subcritical range the actual minimizers for the closed neighborhoods
converge in the global homogeneous Sobolev graph to an actual minimizer for K.
This means convergence in both the scalar L^{p*} and gradient L^p norms. -/
theorem exists_strong_neighborhood_capacity_minimizers (hp : 1 < p) (hpn : p < (n : ℝ))
    (hq : q = (n : ℝ) * p / ((n : ℝ) - p)) {K : Set (Space n)} (hK : IsCompact K) :
    ∃ w ∈ exteriorCapacityClass p q K,
    ∃ W : Ioi (0 : ℝ) → exteriorHomogeneousGraph p q n,
      (∀ r, W r ∈ exteriorCapacityClass p q (cthickening r.val K) ∧
        ∀ z ∈ exteriorCapacityClass p q (cthickening r.val K), ‖(W r).1.2‖^p ≤ ‖z.1.2‖^p) ∧
      (∀ z ∈ exteriorCapacityClass p q K, ‖w.1.2‖^p ≤ ‖z.1.2‖^p) ∧
      WeakPHarmonicPair p Kᶜ (w.1.1 : Space n → ℝ) (w.1.2 : Space n → Space n) ∧
      BMCompactCapacityV2.relativeCapacity p K univ = ENNReal.ofReal (‖w.1.2‖^p) ∧
      Tendsto W atBot (𝓝 w) := by
  classical
  have hp0 := zero_lt_one.trans hp
  have hpq : p ≤ q := by
    rw [hq]
    apply (le_div_iff₀ (sub_pos.mpr hpn)).mpr
    nlinarith [sq_nonneg p]
  obtain ⟨w,hw,hm⟩ := exists_exteriorCapacityClass_minimum p q hp hpn hq hK
  have hex (r : Ioi (0:ℝ)) := exists_exteriorCapacityClass_minimum p q hp hpn hq
    (K := cthickening r.val K) (BMCompact.isCompact_closedNeighborhood hK r.val)
  choose W hWm hWmin using hex
  have hW (r : Ioi (0:ℝ)) : W r ∈ exteriorCapacityClass p q K :=
    admissible_graph_antitone (self_subset_cthickening K) (hWm r)
  have he := capacity_eq_exteriorCapacityClass_minimum_energy p q hp hw hm
  have heR (r : Ioi (0:ℝ)) :=
    capacity_eq_exteriorCapacityClass_minimum_energy p q hp (hWm r) (hWmin r)
  have hlim : Tendsto (fun r : Ioi (0:ℝ) => BMCompactCapacityV2.relativeCapacity p
      (cthickening r.val K) univ) atBot (𝓝 (BMCompactCapacityV2.relativeCapacity p K univ)) := by
    apply (tendsto_comp_coe_Ioi_atBot (f := fun δ : ℝ =>
      BMCompactCapacityV2.relativeCapacity p (cthickening δ K) univ)).mpr
    exact BMCompactCapacityV2.tendsto_relativeCapacity_cthickening p hp0 hK univ
  have hfinite : BMCompactCapacityV2.relativeCapacity p K univ ≠ ∞ := by rw [he]; exact ENNReal.ofReal_ne_top
  have hreal : Tendsto (fun r : Ioi (0:ℝ) => ‖(W r).1.2‖^p) atBot (𝓝 (‖w.1.2‖^p)) := by
    have h := (ENNReal.continuousAt_toReal hfinite).tendsto.comp hlim
    simpa only [Function.comp_def,heR,he,ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using h
  refine ⟨w,hw,W,fun r => ⟨hWm r,hWmin r⟩,hm,
    exteriorCapacityClass_minimum_weakPHarmonic p q hp hpq hK.isClosed w hw hm,he,?_⟩
  obtain ⟨A,hA⟩ := exists_exteriorHomogeneousGradient_antilipschitz (n:=n) p q hp hpn hq
  have hfield : Tendsto (fun r : Ioi (0:ℝ) => (W r).1.2) atBot (𝓝 w.1.2) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let d := ‖w.1.2‖^p
    let R := d + ‖w.1.2‖ + 2
    have hd : 0 ≤ d := Real.rpow_nonneg (norm_nonneg _) _
    obtain ⟨κ,hκ,hgap⟩ := BMCompactBanach.lp_bounded_midpoint_gap
      (E := Space n) (μ := (volume : Measure (Space n))) hp R ε hε
    filter_upwards [hreal.eventually_lt_const (show d < d+min 1 κ from
      lt_add_of_pos_right d (lt_min zero_lt_one hκ))] with r hr
    rw [dist_eq_norm]
    by_contra! hsep
    have hR : ‖(W r).1.2‖ ≤ R := by
      have hnorm : ‖(W r).1.2‖ ≤ ‖(W r).1.2‖^p + 1 := by
        by_cases hb : ‖(W r).1.2‖ ≤ 1
        · linarith [Real.rpow_nonneg (norm_nonneg (W r).1.2) p]
        · linarith [Real.self_le_rpow_of_one_le (le_of_not_ge hb) hp.le]
      dsimp only [R]
      linarith [min_le_left (1:ℝ) κ, norm_nonneg w.1.2]
    have hwR : ‖w.1.2‖ ≤ R := by dsimp only [R]; linarith
    have gap := hgap (W r).1.2 w.1.2 hR hwR hsep
    have hc := (convex_exteriorCapacityClass p q K) (hW r) hw
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
    have hlow := hm _ hc
    change d ≤ ‖(1/2:ℝ) • (W r).1.2 + (1/2:ℝ) • w.1.2‖^p at hlow
    rw [←smul_add] at hlow
    change κ ≤ (‖(W r).1.2‖^p + d)/2 - _ at gap
    linarith [min_le_right (1:ℝ) κ]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hpos : 0 < (A:ℝ)+1 := by positivity
  filter_upwards [(Metric.tendsto_nhds.mp hfield) (ε/((A:ℝ)+1)) (div_pos hε hpos)] with r hr
  have hd := hA.le_mul_dist (W r) w
  change dist (W r) w ≤ (A:ℝ) * dist (W r).1.2 w.1.2 at hd
  have h := (lt_div_iff₀ hpos).mp hr
  nlinarith [(dist_nonneg : 0 ≤ dist (W r).1.2 w.1.2)]

end BMCompactPDE
#print axioms BMCompactPDE.exists_strong_neighborhood_capacity_minimizers
