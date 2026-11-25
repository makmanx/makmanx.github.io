import GradientRegularizedDifference
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The actual averaged Jacobian of the regularized p-flux. The fundamental
theorem of calculus derives its exact flux-difference identity. Its upper bound
retains the actual endpoint-gradient weight, whereas its positive lower bound
may depend on fixed nonzero epsilon. No weak-solution regularity is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def regularizedMeanJacobian (p ε : ℝ) (v w : E) : E →L[ℝ] E :=
  ∫ s in (0:ℝ)..1, fderiv ℝ (fun z : E => (ε^2+‖z‖^2)^((p-2)/2) • z)
    (w+s • (v-w))

omit [CompleteSpace E] in
private theorem upstream_mean_jacobian_continuous
    (p : ℝ) {ε : ℝ} (hε : ε≠0) (v w : E) :
    Continuous (fun s : ℝ => fderiv ℝ (fun z : E => (ε^2+‖z‖^2)^((p-2)/2) • z)
      (w+s • (v-w))) :=
  ((contDiff_regularized_pFlux p hε).continuous_fderiv (by simp)).comp
    (continuous_const.add (continuous_id.smul continuous_const))

/-- The actual segment integral of the Jacobian maps the actual gradient
difference to the exact nonlinear flux difference. -/
theorem regularizedMeanJacobian_apply_sub
    (p : ℝ) {ε : ℝ} (hε : ε≠0) (v w : E) :
    regularizedMeanJacobian p ε v w (v-w)=
      (ε^2+‖v‖^2)^((p-2)/2) • v-(ε^2+‖w‖^2)^((p-2)/2) • w := by
  let F : E → E := fun z => (ε^2+‖z‖^2)^((p-2)/2) • z
  let J : ℝ → E →L[ℝ] E := fun s => fderiv ℝ F (w+s • (v-w))
  have hJ : Continuous J := upstream_mean_jacobian_continuous p hε v w
  have hJI : IntervalIntegrable J volume 0 1 := hJ.intervalIntegrable _ _
  rw [regularizedMeanJacobian,ContinuousLinearMap.intervalIntegral_apply hJI]
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ => F (w+t • (v-w)))
      (J s (v-w)) s := by
    have ha : HasDerivAt (fun t : ℝ => w+t • (v-w)) (v-w) s := by
      simpa only [one_smul,id_eq] using! ((hasDerivAt_id s).smul_const (v-w)).const_add w
    have hF : HasFDerivAt F (fderiv ℝ F (w+s • (v-w))) (w+s • (v-w)) :=
      (hasFDerivAt_regularized_pFlux p hε (w+s • (v-w))).differentiableAt.hasFDerivAt
    simpa only [Function.comp_def] using hF.comp_hasDerivAt s ha
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) ((hJ.clm_apply continuous_const).intervalIntegrable (0:ℝ) 1)
  simpa only [J,F,one_smul,zero_smul,add_zero,add_sub_cancel] using hFTC

omit [CompleteSpace E] in
/-- The averaged coefficient has the genuine p-flux growth bound in the
actual endpoint gradients, without an assumed gradient ceiling. -/
theorem norm_regularizedMeanJacobian_le
    {p ε : ℝ} (hp : 2≤p) (hε : ε≠0) (v w : E) :
    ‖regularizedMeanJacobian p ε v w‖≤
      (p-1)*(ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2) := by
  let M := max ‖v‖ ‖w‖
  have hM : 0≤M := (norm_nonneg v).trans (le_max_left _ _)
  have hv : v∈closedBall (0:E) M := by
    simpa only [mem_closedBall,dist_zero_right,M] using le_max_left ‖v‖ ‖w‖
  have hw : w∈closedBall (0:E) M := by
    simpa only [mem_closedBall,dist_zero_right,M] using le_max_right ‖v‖ ‖w‖
  have hb : ∀ s∈Set.uIoc (0:ℝ) 1,
      ‖fderiv ℝ (fun z : E => (ε^2+‖z‖^2)^((p-2)/2) • z) (w+s • (v-w))‖≤
        (p-1)*(ε^2+M^2)^((p-2)/2) := by
    intro s hs
    have hs01 : s∈Icc (0:ℝ) 1 := by
      have hs' : s∈Ioc (0:ℝ) 1 := by
        simpa only [Set.uIoc_of_le (by norm_num : (0:ℝ)≤1)] using hs
      exact ⟨hs'.1.le,hs'.2⟩
    have hx : w+s • (v-w)∈closedBall (0:E) M :=
      (convex_closedBall (0:E) M).add_smul_sub_mem hw hv hs01
    have hxM : ‖w+s • (v-w)‖≤M := by
      simpa only [mem_closedBall,dist_zero_right] using hx
    apply (regularized_pFlux_jacobian_norm_le_ge_two hp hε _).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith : 0≤p-1)
    exact Real.rpow_le_rpow (by positivity)
      (add_le_add le_rfl ((sq_le_sq₀ (norm_nonneg _) hM).mpr hxM))
      (by linarith : 0≤(p-2)/2)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [regularizedMeanJacobian,sub_zero,abs_one,mul_one,M] using hh

set_option maxHeartbeats 1200000 in
/-- Fixed nonzero epsilon gives an actual positive ellipticity lower bound
for the averaged coefficient, valid on every test vector. -/
theorem regularizedMeanJacobian_quadratic_lower
    {p ε : ℝ} (hp : 2≤p) (hε : ε≠0) (v w z : E) :
    (ε^2)^((p-2)/2)*‖z‖^2≤ inner ℝ (regularizedMeanJacobian p ε v w z) z := by
  let J : ℝ → E →L[ℝ] E := fun s =>
    fderiv ℝ (fun a : E => (ε^2+‖a‖^2)^((p-2)/2) • a) (w+s • (v-w))
  have hJ : Continuous J := upstream_mean_jacobian_continuous p hε v w
  have hJz : Continuous (fun s => J s z) := hJ.clm_apply continuous_const
  have hI : IntervalIntegrable (fun s => inner ℝ z (J s z)) volume 0 1 :=
    (continuous_const.inner hJz).intervalIntegrable _ _
  have hpoint (s : ℝ) : (ε^2)^((p-2)/2)*‖z‖^2≤ inner ℝ z (J s z) := by
    have hl := regularized_pFlux_jacobian_quadratic_lower p hε (w+s • (v-w)) z
    rw [min_eq_left (by linarith : (1:ℝ)≤p-1),one_mul] at hl
    have hm := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (sq_nonneg ε) (le_add_of_nonneg_right (sq_nonneg ‖w+s • (v-w)‖))
        (by linarith : 0≤(p-2)/2)) (sq_nonneg ‖z‖)
    exact hm.trans (by simpa only [J,real_inner_comm z] using hl)
  have hmono := intervalIntegral.integral_mono_on (a:=(0:ℝ)) (b:=1)
    (by norm_num) intervalIntegrable_const hI (fun s _ => hpoint s)
  have hlinear := (innerSL ℝ z).intervalIntegral_comp_comm (μ:=volume)
    (hJz.intervalIntegrable (μ:=volume) (0:ℝ) 1)
  rw [←ContinuousLinearMap.intervalIntegral_apply (hJ.intervalIntegrable (0:ℝ) 1)] at hlinear
  simpa only [intervalIntegral.integral_const,sub_zero,one_smul,
    coe_innerSL_apply,regularizedMeanJacobian,J,real_inner_comm] using hmono.trans_eq hlinear

end BMCompactPDE
#print axioms BMCompactPDE.regularizedMeanJacobian_apply_sub
#print axioms BMCompactPDE.norm_regularizedMeanJacobian_le
#print axioms BMCompactPDE.regularizedMeanJacobian_quadratic_lower
