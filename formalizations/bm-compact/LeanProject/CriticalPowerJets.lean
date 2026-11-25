import CriticalPowerProfile

/-! Actual second-order flatness of the smooth adaptive power penalties.
This prepares critical test functions; no viscosity comparison is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem gradient_criticalPowerPenalty_ne_zero {q : ℝ} (hq : 1 < q)
    {x : E} (hx : x ≠ 0) : gradient (criticalPowerPenalty q : E → ℝ) x ≠ 0 := by
  rw [gradient_criticalPowerPenalty hq]
  exact smul_ne_zero (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _).ne' hx

theorem criticalPowerPenalty_pos_of_ne_zero {q : ℝ} (hq : 0 < q)
    {x : E} (hx : x ≠ 0) : 0 < criticalPowerPenalty q x := by
  exact mul_pos (inv_pos.mpr hq) (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _)

theorem actualHessianEnd_criticalPowerPenalty_even_zero {k : ℕ} (hk : 2 ≤ k) :
    BMCompactAnalytic.actualHessianEnd
      (criticalPowerPenalty ((2*k : ℕ) : ℝ) : E → ℝ) 0 = 0 := by
  have hq : (2 : ℝ) < ((2*k : ℕ) : ℝ) := by
    have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    push_cast
    linarith
  have hc : ContDiffAt ℝ 2 (criticalPowerPenalty ((2*k : ℕ) : ℝ) : E → ℝ) 0 :=
    ((contDiff_criticalPowerPenalty_even (E := E) k).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  rw [←fderiv_gradient_eq_actualHessianEnd hc,
    (hasFDerivAt_gradient_criticalPowerPenalty_zero hq).fderiv]
  rfl

theorem actualLaplacian_criticalPowerPenalty_even_zero {k : ℕ} (hk : 2 ≤ k) :
    BMCompactAnalytic.actualLaplacian
      (criticalPowerPenalty ((2*k : ℕ) : ℝ) : E → ℝ) 0 = 0 := by
  rw [BMCompactAnalytic.actualLaplacian,actualHessianEnd_criticalPowerPenalty_even_zero hk,
    map_zero]

theorem actualHessian_criticalPowerPenalty_even_zero {k : ℕ} (hk : 2 ≤ k) (e f : E) :
    BMCompactAnalytic.actualHessian
      (criticalPowerPenalty ((2*k : ℕ) : ℝ) : E → ℝ) 0 e f = 0 := by
  have hh := congrArg (fun A : E →ₗ[ℝ] E => A e)
    (actualHessianEnd_criticalPowerPenalty_even_zero (E := E) hk)
  change (toDual ℝ E).symm
    (BMCompactAnalytic.actualHessian
      (criticalPowerPenalty ((2*k : ℕ) : ℝ) : E → ℝ) 0 e) = 0 at hh
  have hd := congrArg (toDual ℝ E) hh
  rw [(toDual ℝ E).apply_symm_apply,map_zero] at hd
  exact congrArg (fun L : E →L[ℝ] ℝ => L f) hd

end BMCompactPDE
#print axioms BMCompactPDE.actualHessianEnd_criticalPowerPenalty_even_zero
#print axioms BMCompactPDE.actualLaplacian_criticalPowerPenalty_even_zero
#print axioms BMCompactPDE.actualHessian_criticalPowerPenalty_even_zero
#print axioms BMCompactPDE.gradient_criticalPowerPenalty_ne_zero
#print axioms BMCompactPDE.criticalPowerPenalty_pos_of_ne_zero
