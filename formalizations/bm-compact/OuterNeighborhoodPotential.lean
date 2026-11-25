import UpstreamBoundaryInteriorBall
import UpstreamBoundaryExteriorComparison
import CapacityNeighborhood
import LpDominatedLimit
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- A continuous unit potential from the smooth-test variational construction.
The energy refers to the original, independently defined capacity. -/
structure ContinuousUnitCapacityData {n : ℕ} (p : ℝ) (K : Set (Space n)) where
  scalar : Space n → ℝ
  field : Space n → Space n
  continuous_scalar : Continuous scalar
  unit : ∀ x ∈ K, scalar x = 1
  scalarLp : MemLp scalar (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) volume
  harmonic : WeakPHarmonicPair p Kᶜ scalar field
  bounds : ∀ x, 0 ≤ scalar x ∧ scalar x ≤ 1
  decay : Tendsto scalar (cocompact (Space n)) (𝓝 0)
  energy : BMCompactCapacityV2.relativeCapacity p K univ =
    ENNReal.ofReal (∫ x, ‖field x‖ ^ p ∂volume)

/-- The weak exterior comparison orders the actual potentials for nested compacts. -/
theorem ContinuousUnitCapacityData.le_of_subset {n : ℕ} {p : ℝ} (hn : 2 ≤ n)
    {K L : Set (Space n)} (hL : IsCompact L) (hKL : K ⊆ L)
    (u : ContinuousUnitCapacityData p K) (v : ContinuousUnitCapacityData p L) :
    ∀ x, u.scalar x ≤ v.scalar x := by
  have hb (x : Space n) (hx : x ∈ L) : u.scalar x ≤ v.scalar x :=
    (v.unit x hx) ▸ (u.bounds x).2
  have hlim : Tendsto (fun x => u.scalar x - v.scalar x) (cocompact (Space n)) (𝓝 0) := by
    simpa using u.decay.sub v.decay
  have ho := WeakPHarmonicPair.leOn_compl_of_continuous_boundary_order_and_infinity_order hL hn
    (u.harmonic.mono (compl_subset_compl.mpr hKL) hL.isClosed.isOpen_compl)
    v.harmonic u.continuous_scalar v.continuous_scalar hb
    (fun ε hε => hlim.eventually_lt_const hε)
  intro x
  by_cases h : x ∈ L
  · exact hb x h
  · exact ho x h

/-- The all-radius outer scalar for an arbitrary compact set. Every approximating
field is chosen from actual smooth-test minimization. The limit is pointwise
at every point, and the convergence in the critical Sobolev norm is global
along every decreasing null sequence of positive radii. -/
theorem exists_subcritical_outer_neighborhood_potential
    {n : ℕ} {p : ℝ} (hp : 1 < p) (hpn : p < (n : ℝ))
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ U : (r : Set.Ioi (0 : ℝ)) → ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val K),
    ∃ v : Space n → ℝ,
      (∀ x, Monotone (fun r => (U r).scalar x)) ∧
      (∀ x, Tendsto (fun r => (U r).scalar x) atBot (𝓝 (v x))) ∧
      UpperSemicontinuous v ∧ (∀ x, 0 ≤ v x ∧ v x ≤ 1) ∧ (∀ x ∈ K, v x = 1) ∧
      Tendsto v (cocompact (Space n)) (𝓝 0) ∧
      MemLp v (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) volume ∧
      ∀ r : ℕ → Set.Ioi (0 : ℝ), Antitone r → Tendsto r atTop atBot →
        Tendsto (fun j => eLpNorm ((U (r j)).scalar - v)
          (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) volume) atTop (𝓝 0) := by
  classical
  let R := {r : ℝ // 0 < r}
  let one : R := ⟨(1 : ℝ), (by norm_num : (0:ℝ)<1)⟩
  let _ : Nonempty R := ⟨one⟩
  have hn1 : 1 < n := by exact_mod_cast hp.trans hpn
  have hn : 2 ≤ n := by omega
  have hex (r : R) : Nonempty (ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val K)) := by
    obtain ⟨u,g,hc,hunit,hu,-,-,hh,hbounds,hdecay,henergy,-⟩ :=
      exists_continuous_unit_capacity_potential_closedNeighborhood hp hpn hK r.property
    exact ⟨⟨u,g,hc,hunit,hu,hh,hbounds,hdecay,henergy⟩⟩
  let U := fun r : R => (hex r).some
  have hmono (x : Space n) : Monotone (fun r : R => (U r).scalar x) := by
    intro r s hrs
    exact (U r).le_of_subset hn (BMCompact.isCompact_closedNeighborhood hK s.val)
      (BMCompact.closedNeighborhood_mono K hrs) (U s) x
  let v : Space n → ℝ := fun x => ⨅ r : R, (U r).scalar x
  have hb (x : Space n) : BddBelow (range (fun r : R => (U r).scalar x)) :=
    ⟨0, forall_mem_range.mpr (fun r => ((U r).bounds x).1)⟩
  have hvle (x : Space n) (r : R) : v x ≤ (U r).scalar x := ciInf_le (hb x) r
  have hv0 (x : Space n) : 0 ≤ v x := le_ciInf (fun r => ((U r).bounds x).1)
  have hpoint (x : Space n) : Tendsto (fun r : R => (U r).scalar x) atBot (𝓝 (v x)) :=
    tendsto_atBot_ciInf (hmono x) (hb x)
  have husc : UpperSemicontinuous v :=
    upperSemicontinuous_ciInf hb (fun r => (U r).continuous_scalar.upperSemicontinuous)
  have hmeas : AEStronglyMeasurable v volume := husc.measurable.aestronglyMeasurable
  refine ⟨U, v, hmono, hpoint, husc, (fun x => ⟨hv0 x,(hvle x one).trans ((U one).bounds x).2⟩),
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact le_antisymm ((hvle x one).trans ((U one).bounds x).2) (le_ciInf fun r =>
      ((U r).unit x (BMCompact.subset_closedNeighborhood K r.val hx)).ge)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (U one).decay hv0
      (fun x => hvle x one)
  · apply (U one).scalarLp.of_le hmeas
    exact Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hv0 x), abs_of_nonneg ((U one).bounds x).1]
        using hvle x one
  · intro r hr hr0
    have hq : 0 < (n : ℝ) * p / ((n : ℝ) - p) :=
      div_pos (mul_pos ((zero_lt_one.trans hp).trans hpn) (zero_lt_one.trans hp)) (sub_pos.mpr hpn)
    apply tendsto_eLpNorm_zero_of_dominated (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top
      (fun j => (U (r j)).continuous_scalar.aestronglyMeasurable.sub hmeas) (U (r 0)).scalarLp
    · intro j
      apply Eventually.of_forall
      intro x
      simp only [Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hvle x (r j))),
        abs_of_nonneg ((U (r 0)).bounds x).1]
      exact (sub_le_self _ (hv0 x)).trans (hmono x (hr (Nat.zero_le j)))
    · exact Eventually.of_forall fun x => by
        simpa only [Pi.sub_apply, Function.comp_def, sub_self] using! ((hpoint x).comp hr0).sub_const (v x)

end BMCompactPDE
#print axioms BMCompactPDE.ContinuousUnitCapacityData.le_of_subset
#print axioms BMCompactPDE.exists_subcritical_outer_neighborhood_potential
