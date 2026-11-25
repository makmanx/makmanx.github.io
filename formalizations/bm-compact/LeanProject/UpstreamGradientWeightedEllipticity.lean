import UpstreamGradientMeanJacobian
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual common-weight ellipticity of the averaged flux Jacobian. The same
constructed segment weight controls its lower quadratic form and operator norm
with ratio p-1. The weight can degenerate as epsilon tends to zero; this is not
uniform unweighted ellipticity, a gradient bound, or a full Moser iteration. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def regularizedMeanWeight (p ε : ℝ) (v w : E) : ℝ :=
  ∫ s in (0:ℝ)..1,(ε^2+‖w+s • (v-w)‖^2)^((p-2)/2)

/-- In finite-dimensional gradient space the actual mean weight is continuous
in the two endpoint values, hence its composition with actual weak-gradient
fields is measurably usable without an additional coefficient premise. -/
theorem continuous_regularizedMeanWeight [FiniteDimensional ℝ E]
    (p : ℝ) {ε : ℝ} (hε : ε≠0) :
    Continuous (fun vw : E×E => regularizedMeanWeight p ε vw.1 vw.2) := by
  have hpath : Continuous (fun a : (E×E)×ℝ => a.1.2+a.2 • (a.1.1-a.1.2)) := by
    fun_prop
  have hc : Continuous (fun a : (E×E)×ℝ =>
      (ε^2+‖a.1.2+a.2 • (a.1.1-a.1.2)‖^2)^((p-2)/2)) :=
    (continuous_const.add (hpath.norm.pow 2)).rpow_const (fun a => Or.inl
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hε) (sq_nonneg _)).ne')
  have hi := continuous_parametric_integral_of_continuous (μ:=volume)
    (f:=fun vw : E×E => fun s : ℝ => (ε^2+‖vw.2+s • (vw.1-vw.2)‖^2)^((p-2)/2))
    hc (isCompact_Icc (a:=(0:ℝ)) (b:=1))
  simpa only [regularizedMeanWeight,intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_Icc_eq_integral_Ioc] using hi

set_option maxHeartbeats 1200000 in
/-- A genuine positive segment weight supplies BOTH ellipticity sides for
the actual averaged Jacobian, with common ratio p-1 independent of epsilon
and endpoint gradients. Its absolute size is not asserted to be uniform. -/
theorem regularizedMeanJacobian_weighted_ellipticity [CompleteSpace E]
    {p ε : ℝ} (hp : 2≤p) (hε : ε≠0) (v w : E) :
    0<regularizedMeanWeight p ε v w ∧
      regularizedMeanWeight p ε v w≤(ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2) ∧
      ‖regularizedMeanJacobian p ε v w‖≤(p-1)*regularizedMeanWeight p ε v w ∧
      ∀ z : E,regularizedMeanWeight p ε v w*‖z‖^2 ≤
        inner ℝ (regularizedMeanJacobian p ε v w z) z := by
  let W : ℝ → ℝ := fun s => (ε^2+‖w+s • (v-w)‖^2)^((p-2)/2)
  let J : ℝ → E →L[ℝ] E := fun s =>
    fderiv ℝ (fun a : E => (ε^2+‖a‖^2)^((p-2)/2) • a) (w+s • (v-w))
  have hpath : Continuous (fun s : ℝ => w+s • (v-w)) := by fun_prop
  have hW : Continuous W := (continuous_const.add (hpath.norm.pow 2)).rpow_const
    (fun _ => Or.inl (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hε) (sq_nonneg _)).ne')
  have hJ : Continuous J := ((contDiff_regularized_pFlux p hε).continuous_fderiv
    (by simp)).comp hpath
  have hab : (0:ℝ)≤1 := by norm_num
  have hlow : (ε^2)^((p-2)/2)≤regularizedMeanWeight p ε v w := by
    have hi := intervalIntegral.integral_mono_on (a:=(0:ℝ)) (b:=1) hab
      intervalIntegrable_const (hW.intervalIntegrable (μ:=volume) 0 1)
      (fun s _ => Real.rpow_le_rpow (sq_nonneg ε)
        (le_add_of_nonneg_right (sq_nonneg ‖w+s • (v-w)‖))
        (by linarith : 0≤(p-2)/2))
    simpa only [intervalIntegral.integral_const,sub_zero,one_smul,regularizedMeanWeight,W] using hi
  refine ⟨(Real.rpow_pos_of_pos (sq_pos_of_ne_zero hε) _).trans_le hlow,?_,?_,?_⟩
  · let M := max ‖v‖ ‖w‖
    have hM : 0≤M := (norm_nonneg v).trans (le_max_left _ _)
    have hv : v∈closedBall (0:E) M := by
      simpa only [mem_closedBall,dist_zero_right,M] using le_max_left ‖v‖ ‖w‖
    have hw : w∈closedBall (0:E) M := by
      simpa only [mem_closedBall,dist_zero_right,M] using le_max_right ‖v‖ ‖w‖
    have hi := intervalIntegral.integral_mono_on (a:=(0:ℝ)) (b:=1) hab
      (hW.intervalIntegrable (μ:=volume) 0 1) intervalIntegrable_const (fun s hs => by
        have hx := (convex_closedBall (0:E) M).add_smul_sub_mem hw hv hs
        have hxM : ‖w+s • (v-w)‖≤M := by
          simpa only [mem_closedBall,dist_zero_right] using hx
        exact Real.rpow_le_rpow (by positivity)
          (add_le_add le_rfl ((sq_le_sq₀ (norm_nonneg _) hM).mpr hxM))
          (by linarith : 0≤(p-2)/2))
    simpa only [intervalIntegral.integral_const,sub_zero,one_smul,regularizedMeanWeight,W,M] using hi
  · have hcmp := intervalIntegral.integral_mono_on (a:=(0:ℝ)) (b:=1) hab
      (hJ.norm.intervalIntegrable (μ:=volume) 0 1)
      ((continuous_const.mul hW).intervalIntegrable (μ:=volume) 0 1)
      (fun s _ => regularized_pFlux_jacobian_norm_le_ge_two hp hε (w+s • (v-w)))
    have hn := intervalIntegral.norm_integral_le_integral_norm (μ:=volume) (f:=J) hab
    change ‖∫ s in (0:ℝ)..1,J s‖≤(p-1)*(∫ s in (0:ℝ)..1,W s)
    exact hn.trans (hcmp.trans_eq (intervalIntegral.integral_const_mul (p-1) W))
  · intro z
    have hJz : Continuous (fun s => J s z) := hJ.clm_apply continuous_const
    have hcmp := intervalIntegral.integral_mono_on (a:=(0:ℝ)) (b:=1) hab
      ((hW.mul continuous_const).intervalIntegrable (μ:=volume) 0 1)
      ((continuous_const.inner hJz).intervalIntegrable (μ:=volume) 0 1)
      (fun s _ => by
        have hl := regularized_pFlux_jacobian_quadratic_lower p hε (w+s • (v-w)) z
        rw [min_eq_left (by linarith : (1:ℝ)≤p-1),one_mul] at hl
        simpa only [W,J,Pi.mul_apply,real_inner_comm z] using hl)
    have hlinear := (innerSL ℝ z).intervalIntegral_comp_comm (μ:=volume)
      (hJz.intervalIntegrable (μ:=volume) (0:ℝ) 1)
    rw [←ContinuousLinearMap.intervalIntegral_apply (hJ.intervalIntegrable (μ:=volume) (0:ℝ) 1)] at hlinear
    have hleft : (∫ s in (0:ℝ)..1,W s*‖z‖^2)=regularizedMeanWeight p ε v w*‖z‖^2 := by
      exact intervalIntegral.integral_mul_const (‖z‖^2) W
    change (∫ s in (0:ℝ)..1,W s*‖z‖^2)≤_ at hcmp
    rw [hleft] at hcmp
    simpa only [coe_innerSL_apply,regularizedMeanJacobian,J,real_inner_comm] using
      hcmp.trans_eq hlinear

end BMCompactPDE
#print axioms BMCompactPDE.continuous_regularizedMeanWeight
#print axioms BMCompactPDE.regularizedMeanJacobian_weighted_ellipticity
