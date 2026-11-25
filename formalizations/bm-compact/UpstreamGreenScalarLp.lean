import LpDominatedLimit
import RadialSobolev

/-! Actual scalar Lp convergence on bounded windows. The common pointwise
ceiling and pointwise convergence are explicit; no Lp convergence or limit
bound is assumed. Continuity on the compact closure supplies actual MemLp. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

theorem scalar_Lp_limit_on_bounded_of_pointwise_bounded
    {n : ℕ} {p : ℝ} (hp : 1<p) {D : Set (Space n)}
    (hDb : Bornology.IsBounded D) (hDm : MeasurableSet D)
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (huc : ∀ j,ContinuousOn (u j) (closure D))
    (hvc : ContinuousOn v (closure D)) {B : ℝ} (hB : 0≤B)
    (hbound : ∀ j,∀ x∈D,|u j x|≤B)
    (hpoint : ∀ x∈D,Tendsto (fun j=>u j x) atTop (𝓝 (v x))) :
    MemLp v (ENNReal.ofReal p) (volume.restrict D) ∧
      Tendsto (fun j=>eLpNorm (u j-v) (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0) := by
  have hv := memLp_on_bounded_of_continuousOn_closure (ENNReal.ofReal p) hDb hDm hvc
  have hu (j : ℕ) := memLp_on_bounded_of_continuousOn_closure (ENNReal.ofReal p) hDb hDm (huc j)
  haveI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hDb.measure_lt_top.ne
  have hvbound (x : Space n) (hx : x∈D) : |v x|≤B :=
    le_of_tendsto ((hpoint x hx).abs) (Eventually.of_forall (fun j=>hbound j x hx))
  refine ⟨hv,?_⟩
  apply tendsto_eLpNorm_zero_of_dominated
    ((ENNReal.ofReal_pos.mpr (zero_lt_one.trans hp)).ne') ENNReal.ofReal_ne_top
    (fun j=>(hu j).1.sub hv.1) (memLp_const (2*B))
  · intro j
    filter_upwards [ae_restrict_mem hDm] with x hx
    simp only [Pi.sub_apply,Real.norm_eq_abs]
    calc
      |u j x-v x|≤|u j x|+|v x| := abs_sub _ _
      _≤2*B := by linarith only [hbound j x hx,hvbound x hx]
      _=|2*B| := (abs_of_nonneg (by positivity)).symm
  · filter_upwards [ae_restrict_mem hDm] with x hx
    simpa only [Pi.sub_apply,sub_self] using (hpoint x hx).sub_const (v x)

end BMCompactPDE
#print axioms BMCompactPDE.scalar_Lp_limit_on_bounded_of_pointwise_bounded
