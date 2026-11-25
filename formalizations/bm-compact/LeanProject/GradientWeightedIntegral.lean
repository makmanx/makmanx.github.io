import GradientRegularizedCaccioppoli
import GradientLocalQuotient

/-! Actual weighted quadratic energy is bounded by genuine Lp field norms,
p>=2. This supplies the integral step for uniform difference quotients.
No Hessian, gradient bound or desired energy estimate is an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal
namespace BMCompactPDE

private theorem gradient_weighted_square_pointwise {n : ℕ} {p : ℝ} (hp : 2≤p)
    (ε : ℝ) (v w : Space n) (z : ℝ) :
    (ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2)*‖z‖^2≤(|ε|+‖v‖+‖w‖+‖z‖)^p := by
  let H := |ε|+‖v‖+‖w‖+‖z‖
  have hH : 0≤H := by dsimp only [H];positivity
  have hM0 : 0≤max ‖v‖ ‖w‖ := (norm_nonneg _).trans (le_max_left _ _)
  have hMle : max ‖v‖ ‖w‖≤‖v‖+‖w‖ := max_le
    (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hs : Real.sqrt (ε^2+(max ‖v‖ ‖w‖)^2)≤H := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hH,?_⟩
    have hsq : ε^2+(max ‖v‖ ‖w‖)^2≤(|ε|+max ‖v‖ ‖w‖)^2 := by
      nlinarith only [mul_nonneg (abs_nonneg ε) hM0,sq_abs ε]
    exact hsq.trans ((sq_le_sq₀ (add_nonneg (abs_nonneg _) hM0) hH).mpr
      (by dsimp only [H];linarith only [hMle,norm_nonneg z]))
  have hW := Real.rpow_le_rpow (Real.sqrt_nonneg _) hs (sub_nonneg.mpr hp)
  have hweight : (Real.sqrt (ε^2+(max ‖v‖ ‖w‖)^2))^(p-2)=
      (ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (add_nonneg (sq_nonneg ε) (sq_nonneg _))]
    congr 1
    ring
  rw [hweight] at hW
  have hZ : ‖z‖^2≤H^2 := (sq_le_sq₀ (norm_nonneg _) hH).mpr
    (by dsimp only [H];linarith only [abs_nonneg ε,norm_nonneg v,norm_nonneg w])
  have hprod := mul_le_mul hW hZ (sq_nonneg _) (Real.rpow_nonneg hH _)
  have hpower : H^(p-2)*H^2=H^p := by
    by_cases hzero : H=0
    · norm_num only [hzero,Real.zero_rpow (by linarith : p≠0),mul_zero]
    · rw [←Real.rpow_two,←Real.rpow_add (lt_of_le_of_ne hH (Ne.symm hzero))]
      congr 1
      ring
  exact hprod.trans_eq hpower

set_option maxHeartbeats 1200000 in
theorem regularized_weighted_square_integral_bound {n : ℕ} {p ε : ℝ} (hp : 2≤p)
    {μ : Measure (Space n)} [IsFiniteMeasure μ]
    {g h : Space n → Space n} {z : Space n → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) μ) (hh : MemLp h (ENNReal.ofReal p) μ)
    (hz : MemLp z (ENNReal.ofReal p) μ) :
    (∫ x,(ε^2+(max ‖g x‖ ‖h x‖)^2)^((p-2)/2)*‖z x‖^2 ∂μ)≤
      ((eLpNorm (fun _ : Space n => |ε|) (ENNReal.ofReal p) μ).toReal+
        (eLpNorm g (ENNReal.ofReal p) μ).toReal+
        (eLpNorm h (ENNReal.ofReal p) μ).toReal+
        (eLpNorm z (ENNReal.ofReal p) μ).toReal)^p := by
  have hp0 : 0<p := lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) hp
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith : 1≤p)⟩
  have hc : MemLp (fun _ : Space n => |ε|) (ENNReal.ofReal p) μ := memLp_const |ε|
  let C := hc.toLp (fun _ : Space n => |ε|)
  let G := hg.norm.toLp (fun x => ‖g x‖)
  let H := hh.norm.toLp (fun x => ‖h x‖)
  let Z := hz.norm.toLp (fun x => ‖z x‖)
  let V := C+G+H+Z
  have hAE : V=ᵐ[μ] (fun x => |ε|+‖g x‖+‖h x‖+‖z x‖) := by
    filter_upwards [Lp.coeFn_add (C+G+H) Z,Lp.coeFn_add (C+G) H,Lp.coeFn_add C G,
      hc.coeFn_toLp,hg.norm.coeFn_toLp,hh.norm.coeFn_toLp,hz.norm.coeFn_toLp]
      with x ha hb hd hCx hGx hHx hZx
    change (C+G+H+Z : Lp ℝ (ENNReal.ofReal p) μ) x=_
    rw [ha,Pi.add_apply,hb,Pi.add_apply,hd,Pi.add_apply,hCx,hGx,hHx,hZx]
  have hpow : (fun x => ‖V x‖^p)=ᵐ[μ] (fun x => (|ε|+‖g x‖+‖h x‖+‖z x‖)^p) := by
    filter_upwards [hAE] with x hx
    rw [hx,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hVI := (BMCompactNonlinear.lp_norm_rpow_integrable hp0 V).congr hpow
  have hE : (∫ x,(|ε|+‖g x‖+‖h x‖+‖z x‖)^p ∂μ)=‖V‖^p :=
    (integral_congr_ae hpow).symm.trans
      (BMCompactNonlinear.lp_norm_rpow_eq_integral hp0 V).symm
  have hVnorm : ‖V‖≤‖C‖+‖G‖+‖H‖+‖Z‖ := by
    calc
      _≤‖C+G+H‖+‖Z‖ := norm_add_le _ _
      _≤(‖C+G‖+‖H‖)+‖Z‖ := add_le_add (norm_add_le _ _) le_rfl
      _≤_ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
  have hbound : ‖V‖≤(eLpNorm (fun _ : Space n => |ε|) (ENNReal.ofReal p) μ).toReal+
      (eLpNorm g (ENNReal.ofReal p) μ).toReal+
      (eLpNorm h (ENNReal.ofReal p) μ).toReal+
      (eLpNorm z (ENNReal.ofReal p) μ).toReal := by
    simpa only [C,G,H,Z,Lp.norm_toLp,eLpNorm_norm] using hVnorm
  have hi := integral_mono (integrable_regularized_weighted_square hp hg hh hz) hVI
    (fun x => gradient_weighted_square_pointwise hp ε (g x) (h x) (z x))
  rw [hE] at hi
  exact hi.trans (Real.rpow_le_rpow (norm_nonneg _) hbound hp0.le)

end BMCompactPDE
#print axioms BMCompactPDE.regularized_weighted_square_integral_bound
