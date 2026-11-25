import BMCompactChecked

/-! Actual concave scalar strictification of the normalized p-Laplacian.
Every gradient and Hessian is the actual derivative. Noncriticality of the
comparator remains explicit; this does not solve arbitrary critical comparison. -/
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace
open scoped Topology ContDiff BigOperators
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def criticalConcaveTransform (δ K M : ℝ) (h : E → ℝ) (x : E) : ℝ :=
  h x + δ*(K-(h x-M)^2)

def criticalConcaveSlope (δ M : ℝ) (h : E → ℝ) (x : E) : ℝ :=
  1-2*δ*(h x-M)

theorem contDiffAt_criticalConcaveTransform {δ K M : ℝ} {h : E → ℝ} {x : E}
    (hh : ContDiffAt ℝ 2 h x) :
    ContDiffAt ℝ 2 (criticalConcaveTransform δ K M h) x := by
  exact hh.add (contDiffAt_const.mul (contDiffAt_const.sub ((hh.sub contDiffAt_const).pow 2)))

theorem fderiv_criticalConcaveTransform {δ K M : ℝ} {h : E → ℝ} {x : E}
    (hh : DifferentiableAt ℝ h x) :
    fderiv ℝ (criticalConcaveTransform δ K M h) x =
      criticalConcaveSlope δ M h x • fderiv ℝ h x := by
  have hd := hh.hasFDerivAt.add
    ((((hh.hasFDerivAt.sub_const M).pow 2).const_sub K).const_mul δ)
  convert! hd.fderiv using 1
  ext e
  simp only [criticalConcaveSlope,ContinuousLinearMap.add_apply,neg_apply,smul_apply,
    smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat,pow_one]
  ring

theorem gradient_criticalConcaveTransform {δ K M : ℝ} {h : E → ℝ} {x : E}
    (hh : DifferentiableAt ℝ h x) :
    gradient (criticalConcaveTransform δ K M h) x =
      criticalConcaveSlope δ M h x • gradient h x := by
  unfold gradient
  rw [fderiv_criticalConcaveTransform hh,map_smul]

theorem actualHessian_criticalConcaveTransform {δ K M : ℝ} {h : E → ℝ} {x : E}
    (hh : ContDiffAt ℝ 2 h x) (e f : E) :
    actualHessian (criticalConcaveTransform δ K M h) x e f =
      criticalConcaveSlope δ M h x * actualHessian h x e f -
        2*δ*(fderiv ℝ h x e)*(fderiv ℝ h x f) := by
  have hh1 := hh.differentiableAt (by norm_num)
  have hD := (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hA := ((hh1.hasFDerivAt.sub_const M).const_mul (2*δ)).const_sub 1
  have hA' : HasFDerivAt (criticalConcaveSlope δ M h)
      ((-2*δ) • fderiv ℝ h x) x := by
    convert! hA using 1
    ext v
    simp only [neg_apply,smul_apply,smul_eq_mul]
    ring
  have hP := hA'.smul hD.hasFDerivAt
  have hP' : HasFDerivAt (fun y => criticalConcaveSlope δ M h y • fderiv ℝ h y)
      (criticalConcaveSlope δ M h x • fderiv ℝ (fderiv ℝ h) x +
        (((-2*δ) • fderiv ℝ h x).smulRight (fderiv ℝ h x))) x := by
    simpa only [Pi.smul_def] using! hP
  have heq : fderiv ℝ (criticalConcaveTransform δ K M h) =ᶠ[𝓝 x]
      (fun y => criticalConcaveSlope δ M h y • fderiv ℝ h y) := by
    filter_upwards [hh.eventually (by simp)] with y hy
    exact fderiv_criticalConcaveTransform (hy.differentiableAt (by norm_num))
  unfold actualHessian
  rw [heq.fderiv_eq,hP'.fderiv]
  simp only [ContinuousLinearMap.add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

theorem actualLaplacian_criticalConcaveTransform {δ K M : ℝ} {h : E → ℝ} {x : E}
    (hh : ContDiffAt ℝ 2 h x) :
    actualLaplacian (criticalConcaveTransform δ K M h) x =
      criticalConcaveSlope δ M h x * actualLaplacian h x - 2*δ*‖gradient h x‖^2 := by
  classical
  let b := stdOrthonormalBasis ℝ E
  rw [actualLaplacian_eq_sum b,actualLaplacian_eq_sum b]
  simp_rw [actualHessian_criticalConcaveTransform hh]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]
  have hs : (∑ i, 2*δ*(fderiv ℝ h x (b i))*(fderiv ℝ h x (b i))) =
      2*δ*‖gradient h x‖^2 := by
    simp_rw [mul_assoc,←pow_two,←inner_gradient_left]
    rw [←Finset.mul_sum,←Finset.mul_sum,b.sum_sq_inner_left]
  rw [hs]

theorem normalizedPLaplacian_criticalConcaveTransform (p : ℝ)
    {δ K M : ℝ} {h : E → ℝ} {x : E}
    (hh : ContDiffAt ℝ 2 h x) (hg : gradient h x ≠ 0)
    (hA : 0 < criticalConcaveSlope δ M h x) :
    normalizedPLaplacian p (criticalConcaveTransform δ K M h) x =
      criticalConcaveSlope δ M h x * normalizedPLaplacian p h x -
        2*δ*(p-1)*‖gradient h x‖^2 := by
  have hn : ‖gradient h x‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have he : fderiv ℝ h x (gradient h x) = ‖gradient h x‖^2 := by
    rw [←inner_gradient_left,real_inner_self_eq_norm_sq]
  unfold normalizedPLaplacian
  rw [actualLaplacian_criticalConcaveTransform hh,
    actualHessian_criticalConcaveTransform hh,
    gradient_criticalConcaveTransform (hh.differentiableAt (by norm_num))]
  simp only [map_smul,smul_apply,smul_eq_mul,norm_smul,Real.norm_eq_abs,abs_of_pos hA]
  rw [he]
  field_simp [hn,hA.ne'] <;> ring

theorem criticalConcaveSlope_pos {δ M : ℝ} {h : E → ℝ} {x : E}
    (hδ : 0 < δ) (hM : h x ≤ M) : 0 < criticalConcaveSlope δ M h x := by
  unfold criticalConcaveSlope
  have hm : 0 ≤ 2*δ*(M-h x) := mul_nonneg (by positivity) (sub_nonneg.mpr hM)
  linarith

theorem normalizedPLaplacian_criticalConcaveTransform_neg
    {p δ K M : ℝ} (hp : 1 < p) (hδ : 0 < δ) {h : E → ℝ} {x : E}
    (hh : ContDiffAt ℝ 2 h x) (hg : gradient h x ≠ 0) (hM : h x ≤ M)
    (hP : normalizedPLaplacian p h x ≤ 0) :
    normalizedPLaplacian p (criticalConcaveTransform δ K M h) x < 0 := by
  have hA := criticalConcaveSlope_pos hδ hM
  rw [normalizedPLaplacian_criticalConcaveTransform p hh hg hA]
  have hnon : criticalConcaveSlope δ M h x * normalizedPLaplacian p h x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hA.le hP
  have hstrict : 0 < 2*δ*(p-1)*‖gradient h x‖^2 := by
    have hn := norm_pos_iff.mpr hg
    positivity
  linarith

end BMCompactAnalytic
#print axioms BMCompactAnalytic.contDiffAt_criticalConcaveTransform
#print axioms BMCompactAnalytic.fderiv_criticalConcaveTransform
#print axioms BMCompactAnalytic.gradient_criticalConcaveTransform
#print axioms BMCompactAnalytic.actualHessian_criticalConcaveTransform
#print axioms BMCompactAnalytic.actualLaplacian_criticalConcaveTransform
#print axioms BMCompactAnalytic.normalizedPLaplacian_criticalConcaveTransform
#print axioms BMCompactAnalytic.criticalConcaveSlope_pos
#print axioms BMCompactAnalytic.normalizedPLaplacian_criticalConcaveTransform_neg
