import RigidNeighborhoodPotential
import UnboundedOpenComparison
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Geometry.Euclidean.Projection

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric EuclideanGeometry AffineSubspace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private instance bisectorNonempty {n : ℕ} (x y : Space n) : Nonempty (perpBisector x y) :=
  ⟨⟨_,midpoint_mem_perpBisector x y⟩⟩

theorem bisector_reflection_swap {n : ℕ} (x y : Space n) :
    reflection (perpBisector x y) y = x := by
  let S := perpBisector x y
  let m := midpoint ℝ x y
  have hv : y -ᵥ m ∈ S.directionᗮ := by
    rw [show S.direction = _ from direction_perpBisector x y]
    apply Submodule.le_orthogonal_orthogonal
    rw [right_vsub_midpoint]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have he := reflection_orthogonal_vadd (midpoint_mem_perpBisector x y) hv
  rw [vsub_vadd] at he
  have hmid : m -ᵥ y = x -ᵥ m := by dsimp only [m];rw [midpoint_vsub_right,left_vsub_midpoint]
  rw [he,neg_vsub_eq_vsub_rev,hmid,vsub_vadd]
  
/-- Whenever the two evaluation radii differ by more than twice the radius
of an enclosing ball, the actual neighborhood potential is ordered at the
two points. No directional derivative or boundary regularity is assumed. -/
theorem ContinuousUnitCapacityData.reflection_far_order {n : ℕ} {p : ℝ} (hp : 1<p)
    (hpn : p<(n:ℝ)) {K : Set (Space n)} (hK : IsCompact K) {δ : ℝ} (hδ : 0<δ)
    (U : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood δ K)) {R : ℝ} (hR : 0<R)
    (hball : BMCompact.closedNeighborhood δ K ⊆ ball 0 R) (x y : Space n)
    (hgap : ‖x‖+2*R ≤ ‖y‖) : U.scalar y ≤ U.scalar x := by
  let L := BMCompact.closedNeighborhood δ K
  let S := perpBisector x y
  let e := reflection S
  have he : e y=x := bisector_reflection_swap x y
  have hK' : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  let L' := BMCompact.closedNeighborhood δ (e ⁻¹' K)
  have hL' : IsCompact L' := BMCompact.isCompact_closedNeighborhood hK' δ
  obtain ⟨v,g,hc,hunit,hu,_,_,hH,hb,hd,hen,_⟩ :=
    exists_continuous_unit_capacity_potential_closedNeighborhood hp hpn hK' hδ
  let V : ContinuousUnitCapacityData p L' := ⟨v,g,hc,hunit,hu,hH,hb,hd,hen⟩
  have hv (w : Space n) : U.scalar (e w) = v w :=
    congrFun (U.rigid_neighborhood_scalar hp hpn hK hδ e V) w
  let H := {w : Space n | dist w y < dist w x}
  let Ω := H ∩ L'ᶜ
  have hHopen : IsOpen H := isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)
  have hopen : IsOpen Ω := hHopen.inter hL'.isClosed.isOpen_compl
  have hsub : H ⊆ Lᶜ := by
    intro z hz hzL
    have hnorm : ‖z‖<R := by simpa only [mem_ball,dist_zero_right] using hball hzL
    have h1 := dist_triangle y z (0:Space n)
    have h2 := dist_triangle z (0:Space n) x
    simp only [dist_zero_right,dist_zero_left,dist_comm y z] at h1 h2
    change dist z y<dist z x at hz
    linarith
  have hboundary (w : Space n) (hw : w ∈ frontier Ω) : U.scalar w ≤ v w := by
    by_cases h : w∈L'
    · rw [hunit w h]
      exact (U.bounds w).2
    have hcH : w∈closure H := (closure_mono inter_subset_left) (frontier_subset_closure hw)
    have hle : dist w y ≤ dist w x := closure_lt_subset_le (continuous_id.dist continuous_const)
      (continuous_id.dist continuous_const) hcH
    have hn : w∉Ω := (hopen.frontier_eq ▸ hw).2
    have heq : dist w x = dist w y := le_antisymm (le_of_not_gt (fun hlt=>hn ⟨hlt,h⟩)) hle
    have hwS : w ∈ S := mem_perpBisector_iff_dist_eq.mpr heq
    have hwfix : e w=w := (reflection_eq_self_iff w).mpr hwS
    simpa only [hwfix] using (hv w).le
  have hxy : y ≠ x := by rintro rfl;linarith
  by_cases hy : y∈L'
  · rw [←he,hv,hunit y hy]
    exact (U.bounds y).2
  have hyΩ : y∈Ω := ⟨by change dist y y < dist y x; simpa using dist_pos.mpr hxy,hy⟩
  have hdec : Tendsto (fun w=>U.scalar w-v w) (cocompact _) (𝓝 0) := by simpa using U.decay.sub hd
  have hn1 : 1<n := by exact_mod_cast hp.trans hpn
  have hh := (U.harmonic.mono (inter_subset_left.trans hsub) hopen).le_of_frontier_and_decay (by omega)
    (hH.mono inter_subset_right hopen) U.continuous_scalar hc hboundary (fun ε hε=>hdec.eventually_lt_const hε) y hyΩ
  simpa only [←hv,he] using hh

end BMCompactPDE
#print axioms BMCompactPDE.bisector_reflection_swap
#print axioms BMCompactPDE.ContinuousUnitCapacityData.reflection_far_order
