import LpDominatedLimit
import Mathlib.Topology.Order.MonotoneConvergence

/-! A raw pointwise limit needs no continuity to converge strongly in Lp on
finite windows. Actual measurable approximants and a common scalar ceiling
supply measurability, Lp membership and the dominated-convergence conclusion.
No pointwise identification with a selected PDE representative is asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- A bounded measurable pointwise scalar limit is genuinely in Lp and is
attained strongly. Continuity of the limit is not an input or a conclusion. -/
theorem raw_scalar_Lp_limit_on_finite_window
    {n : ℕ} {p : ℝ} (hp : 1<p) {D : Set (Space n)}
    (hDm : MeasurableSet D) [IsFiniteMeasure (volume.restrict D)]
    {u : ℕ → Space n → ℝ} {v : Space n → ℝ}
    (hum : ∀ j,AEStronglyMeasurable (u j) (volume.restrict D))
    {B : ℝ} (hB : 0≤B) (hbound : ∀ j,∀ x∈D,|u j x|≤B)
    (hpoint : ∀ x∈D,Tendsto (fun j=>u j x) atTop (𝓝 (v x))) :
    MemLp v (ENNReal.ofReal p) (volume.restrict D) ∧
      Tendsto (fun j=>eLpNorm (u j-v) (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0) := by
  have hvbound (x : Space n) (hx : x∈D) : |v x|≤B :=
    le_of_tendsto ((hpoint x hx).abs) (Eventually.of_forall (fun j=>hbound j x hx))
  have hpointAE : ∀ᵐ x ∂(volume.restrict D),Tendsto (fun j=>u j x) atTop (𝓝 (v x)) := by
    filter_upwards [ae_restrict_mem hDm] with x hx
    exact hpoint x hx
  have hvm := aestronglyMeasurable_of_tendsto_ae atTop hum hpointAE
  have hc : MemLp (fun _ : Space n=>B) (ENNReal.ofReal p) (volume.restrict D) := memLp_const B
  have hv : MemLp v (ENNReal.ofReal p) (volume.restrict D) := by
    apply hc.of_le hvm
    filter_upwards [ae_restrict_mem hDm] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hB] using hvbound x hx
  refine ⟨hv,?_⟩
  apply tendsto_eLpNorm_zero_of_dominated
    ((ENNReal.ofReal_pos.mpr (zero_lt_one.trans hp)).ne') ENNReal.ofReal_ne_top
    (fun j=>(hum j).sub hvm) (memLp_const (2*B))
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
#print axioms BMCompactPDE.raw_scalar_Lp_limit_on_finite_window
