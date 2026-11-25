import SuperViscosity

/-! A genuine fourth-order strictifying upper-test perturbation, with its
actual first and second derivatives zero at the contact point. This changes
no normalized p-Laplacian jet there. -/
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def strictContactQuartic (a x : E) : ℝ := (‖x-a‖^2)^2

theorem contDiff_strictContactQuartic (a : E) :
    ContDiff ℝ ∞ (strictContactQuartic a) :=
  ((contDiff_id.sub contDiff_const).norm_sq ℝ).pow 2

theorem strictContactQuartic_self (a : E) : strictContactQuartic a a=0 := by
  simp [strictContactQuartic]

theorem strictContactQuartic_pos {a x : E} (hx : x≠a) :
    0<strictContactQuartic a x := by
  exact sq_pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)))

theorem fderiv_strictContactQuartic (a x : E) :
    fderiv ℝ (strictContactQuartic a) x =
      (4*‖x-a‖^2) • innerSL ℝ (x-a) := by
  have hn := ((hasFDerivAt_id x).sub_const a).norm_sq
  have hq := hn.pow 2
  convert! hq.fderiv using 1
  ext e
  simp only [id_eq,pow_one,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul]
  ring

theorem fderiv_strictContactQuartic_self (a : E) :
    fderiv ℝ (strictContactQuartic a) a=0 := by
  simp only [fderiv_strictContactQuartic,sub_self,norm_zero,zero_pow (by decide : 2≠0),
    mul_zero,zero_smul]

theorem actualHessian_strictContactQuartic_self (a : E) :
    actualHessian (strictContactQuartic a) a=0 := by
  have heq : fderiv ℝ (strictContactQuartic a) =
      fun y => (4*‖y-a‖^2) • innerSL ℝ (y-a) :=
    funext (fderiv_strictContactQuartic a)
  have hs : HasFDerivAt (fun y : E => 4*‖y-a‖^2) (0 : E →L[ℝ] ℝ) a := by
    have hn := (((hasFDerivAt_id (𝕜 := ℝ) a).sub_const a).norm_sq).const_mul (4 : ℝ)
    convert! hn using 1 <;> simp
  have hv := (innerSL ℝ (E := E)).hasFDerivAt.comp a
    ((hasFDerivAt_id a).sub_const a)
  have hp := hs.smul hv
  have hd : HasFDerivAt (fun y : E => (4*‖y-a‖^2) • innerSL ℝ (y-a))
      (0 : E →L[ℝ] E →L[ℝ] ℝ) a := by
    simpa only [Function.comp_def,sub_self,norm_zero,zero_pow (by decide : 2≠0),
      mul_zero,map_zero,zero_smul,ContinuousLinearMap.zero_smulRight,add_zero] using! hp
  unfold actualHessian
  rw [heq,hd.fderiv]

theorem actualHessian_add_of_contDiffAt_two {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    actualHessian (fun y => f y+g y) x=actualHessian f x+actualHessian g x := by
  have hfn : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono (fun y hy => hy.differentiableAt (by norm_num))
  have hgn : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y :=
    (hg.eventually (by simp)).mono (fun y hy => hy.differentiableAt (by norm_num))
  have heq : fderiv ℝ (fun y => f y+g y) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ f y+fderiv ℝ g y) := by
    filter_upwards [hfn,hgn] with y hyf hyg
    exact fderiv_fun_add hyf hyg
  unfold actualHessian
  rw [heq.fderiv_eq]
  exact fderiv_fun_add
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt_one

theorem gradient_add_strictContactQuartic_self {φ : E → ℝ} {x : E}
    (hφ : DifferentiableAt ℝ φ x) :
    gradient (fun y => φ y+strictContactQuartic x y) x=gradient φ x := by
  unfold gradient
  rw [fderiv_fun_add hφ ((contDiff_strictContactQuartic x).differentiable (by simp) x),
    fderiv_strictContactQuartic_self,add_zero]

theorem actualHessian_add_strictContactQuartic_self {φ : E → ℝ} {x : E}
    (hφ : ContDiffAt ℝ 2 φ x) :
    actualHessian (fun y => φ y+strictContactQuartic x y) x=actualHessian φ x := by
  have hq : ContDiff ℝ 2 (strictContactQuartic x) :=
    (contDiff_strictContactQuartic x).of_le (by decide)
  rw [actualHessian_add_of_contDiffAt_two hφ hq.contDiffAt,
    actualHessian_strictContactQuartic_self]
  ext e f
  simp

theorem normalizedPLaplacian_add_strictContactQuartic_self (p : ℝ)
    {φ : E → ℝ} {x : E} (hφ : ContDiffAt ℝ 2 φ x) :
    normalizedPLaplacian p (fun y => φ y+strictContactQuartic x y) x=
      normalizedPLaplacian p φ x := by
  have hH := actualHessian_add_strictContactQuartic_self hφ
  have hg := gradient_add_strictContactQuartic_self (hφ.differentiableAt (by norm_num))
  simp only [normalizedPLaplacian,actualLaplacian,actualHessianEnd,hH,hg]

end BMCompactAnalytic
#print axioms BMCompactAnalytic.contDiff_strictContactQuartic
#print axioms BMCompactAnalytic.strictContactQuartic_self
#print axioms BMCompactAnalytic.strictContactQuartic_pos
#print axioms BMCompactAnalytic.fderiv_strictContactQuartic
#print axioms BMCompactAnalytic.fderiv_strictContactQuartic_self
#print axioms BMCompactAnalytic.actualHessian_strictContactQuartic_self
#print axioms BMCompactAnalytic.actualHessian_add_of_contDiffAt_two
#print axioms BMCompactAnalytic.gradient_add_strictContactQuartic_self
#print axioms BMCompactAnalytic.actualHessian_add_strictContactQuartic_self
#print axioms BMCompactAnalytic.normalizedPLaplacian_add_strictContactQuartic_self
