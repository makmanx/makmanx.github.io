import BMCompactChecked
import Mathlib.Analysis.Normed.Group.Bounded

/-! Actual quadratic barriers for noncritical-test viscosity comparison.
The comparator in the resulting maximum principle can be constant, so its
gradient vanishes everywhere. No general weak-comparator theorem is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def criticalQuadraticBarrier (a : E) (ε C : ℝ) (x : E) : ℝ :=
  C - ε * ‖x-a‖^2

theorem contDiff_criticalQuadraticBarrier (a : E) (ε C : ℝ) :
    ContDiff ℝ ∞ (criticalQuadraticBarrier a ε C) := by
  have hn : ContDiff ℝ ∞ (fun x : E => ‖x-a‖^2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  exact contDiff_const.sub (contDiff_const.mul hn)

theorem fderiv_criticalQuadraticBarrier (a : E) (ε C : ℝ) (x : E) :
    fderiv ℝ (criticalQuadraticBarrier a ε C) x =
      (-2*ε) • innerSL ℝ (x-a) := by
  have hn := ((hasFDerivAt_id x).sub_const a).norm_sq
  have hq := (hn.const_mul ε).const_sub C
  convert! hq.fderiv using 1
  ext e
  simp only [id_eq,neg_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
  ring

theorem gradient_criticalQuadraticBarrier (a : E) (ε C : ℝ) (x : E) :
    gradient (criticalQuadraticBarrier a ε C) x = (-2*ε) • (x-a) := by
  unfold gradient
  rw [fderiv_criticalQuadraticBarrier,map_smul]
  change (-2*ε) • ((toDual ℝ E).symm ((toDual ℝ E) (x-a))) = _
  rw [(toDual ℝ E).symm_apply_apply]

theorem actualHessian_criticalQuadraticBarrier (a : E) (ε C : ℝ) (x e f : E) :
    actualHessian (criticalQuadraticBarrier a ε C) x e f = (-2*ε)*inner ℝ e f := by
  have heq : fderiv ℝ (criticalQuadraticBarrier a ε C) =
      fun y => (-2*ε) • innerSL ℝ (y-a) :=
    funext (fderiv_criticalQuadraticBarrier a ε C)
  have hd := (((innerSL ℝ (E := E)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).sub_const a)).const_smul (-2*ε)
  have hd' : HasFDerivAt (fun y : E => (-2*ε) • innerSL ℝ (y-a))
      ((-2*ε) • innerSL ℝ (E := E)) x := by
    simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_id] using! hd
  unfold actualHessian
  rw [heq,hd'.fderiv]
  simp only [smul_apply,smul_eq_mul]
  rfl

theorem actualHessianEnd_criticalQuadraticBarrier (a : E) (ε C : ℝ) (x : E) :
    actualHessianEnd (criticalQuadraticBarrier a ε C) x =
      (-2*ε) • LinearMap.id := by
  ext e
  change (toDual ℝ E).symm (actualHessian (criticalQuadraticBarrier a ε C) x e) =
    (-2*ε) • e
  apply (toDual ℝ E).injective
  rw [(toDual ℝ E).apply_symm_apply]
  ext f
  simp only [actualHessian_criticalQuadraticBarrier,map_smul,toDual_apply_apply,
    smul_apply,smul_eq_mul]

theorem actualLaplacian_criticalQuadraticBarrier (a : E) (ε C : ℝ) (x : E) :
    actualLaplacian (criticalQuadraticBarrier a ε C) x =
      (-2*ε) * (Module.finrank ℝ E : ℝ) := by
  rw [actualLaplacian,actualHessianEnd_criticalQuadraticBarrier,map_smul,LinearMap.trace_id]
  rfl

theorem gradient_criticalQuadraticBarrier_ne_zero {a x : E} {ε C : ℝ}
    (hε : 0 < ε) (hxa : x ≠ a) :
    gradient (criticalQuadraticBarrier a ε C) x ≠ 0 := by
  rw [gradient_criticalQuadraticBarrier]
  exact smul_ne_zero (mul_ne_zero (by norm_num) hε.ne') (sub_ne_zero.mpr hxa)

theorem normalizedPLaplacian_criticalQuadraticBarrier (p : ℝ)
    {a x : E} {ε C : ℝ} (hε : 0 < ε) (hxa : x ≠ a) :
    normalizedPLaplacian p (criticalQuadraticBarrier a ε C) x =
      (-2*ε) * ((Module.finrank ℝ E : ℝ)+p-2) := by
  have hg := gradient_criticalQuadraticBarrier_ne_zero (C := C) hε hxa
  have hn : ‖gradient (criticalQuadraticBarrier a ε C) x‖^2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
  rw [normalizedPLaplacian,actualLaplacian_criticalQuadraticBarrier,
    actualHessian_criticalQuadraticBarrier,real_inner_self_eq_norm_sq]
  field_simp [hn] <;> ring

theorem normalizedPLaplacian_criticalQuadraticBarrier_neg [Nontrivial E]
    {p ε C : ℝ} (hp : 1 < p) (hε : 0 < ε) {a x : E} (hxa : x ≠ a) :
    normalizedPLaplacian p (criticalQuadraticBarrier a ε C) x < 0 := by
  rw [normalizedPLaplacian_criticalQuadraticBarrier p hε hxa]
  have hn : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hn' : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hn
  exact mul_neg_of_neg_of_pos (by nlinarith) (by linarith)

end BMCompactAnalytic
#print axioms BMCompactAnalytic.contDiff_criticalQuadraticBarrier
#print axioms BMCompactAnalytic.fderiv_criticalQuadraticBarrier
#print axioms BMCompactAnalytic.gradient_criticalQuadraticBarrier
#print axioms BMCompactAnalytic.actualHessian_criticalQuadraticBarrier
#print axioms BMCompactAnalytic.actualHessianEnd_criticalQuadraticBarrier
#print axioms BMCompactAnalytic.actualLaplacian_criticalQuadraticBarrier
#print axioms BMCompactAnalytic.gradient_criticalQuadraticBarrier_ne_zero
#print axioms BMCompactAnalytic.normalizedPLaplacian_criticalQuadraticBarrier
#print axioms BMCompactAnalytic.normalizedPLaplacian_criticalQuadraticBarrier_neg
