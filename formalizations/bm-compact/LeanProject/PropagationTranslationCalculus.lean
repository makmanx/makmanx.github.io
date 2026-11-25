import SuperContinuousBatch
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Actual translation invariance of gradient, Hessian and p-Laplace formulas,
including the precise translated upper test used by diagonal doubling.
Pointwise operator equalities are valid for the total actual derivative
functions; C2 regularity is assumed separately only for the actual C2 test. -/
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactAnalytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_comp_add_right_actual (f : E → ℝ) (a x : E) :
    gradient (fun z => f (z+a)) x = gradient f (x+a) := by
  unfold gradient
  rw [fderiv_comp_add_right]

theorem actualHessian_comp_add_right (f : E → ℝ) (a x : E) :
    actualHessian (fun z => f (z+a)) x = actualHessian f (x+a) := by
  unfold actualHessian
  have he : fderiv ℝ (fun z => f (z+a)) = fun z => fderiv ℝ f (z+a) :=
    funext (fun z => fderiv_comp_add_right a)
  rw [he,fderiv_comp_add_right]

theorem actualLaplacian_comp_add_right (f : E → ℝ) (a x : E) :
    actualLaplacian (fun z => f (z+a)) x = actualLaplacian f (x+a) := by
  simp only [actualLaplacian,actualHessianEnd,actualHessian_comp_add_right]

theorem normalizedPLaplacian_comp_add_right (p : ℝ) (f : E → ℝ) (a x : E) :
    normalizedPLaplacian p (fun z => f (z+a)) x = normalizedPLaplacian p f (x+a) := by
  simp only [normalizedPLaplacian,actualLaplacian_comp_add_right,
    gradient_comp_add_right_actual,actualHessian_comp_add_right]

theorem classicalPLaplacian_comp_add_right (p : ℝ) (f : E → ℝ) (a x : E) :
    classicalPLaplacian p (fun z => f (z+a)) x = classicalPLaplacian p f (x+a) := by
  simp only [classicalPLaplacian,gradient_comp_add_right_actual,
    normalizedPLaplacian_comp_add_right]

private theorem diagonal_translate_eq (v : E → ℝ) (x y : E) (c : ℝ) :
    (fun z => v (z+y-x)+c) = (fun z => v (z+(y-x))+c) := by
  funext z
  congr 2
  abel

theorem contDiffAt_diagonal_translate_add_const {v : E → ℝ} {x y : E}
    (hv : ContDiffAt ℝ 2 v y) (c : ℝ) :
    ContDiffAt ℝ 2 (fun z => v (z+y-x)+c) x := by
  have hxy : x+(y-x)=y := by abel
  have hv' : ContDiffAt ℝ 2 v (x+(y-x)) := by simpa only [hxy] using hv
  rw [diagonal_translate_eq v x y c]
  exact (hv'.comp x (contDiffAt_id.add contDiffAt_const)).add contDiffAt_const

variable [FiniteDimensional ℝ E]

theorem gradient_diagonal_translate_add_const (v : E → ℝ) (x y : E) (c : ℝ) :
    gradient (fun z => v (z+y-x)+c) x = gradient v y := by
  rw [diagonal_translate_eq v x y c,gradient_add_const,gradient_comp_add_right_actual]
  congr 1
  abel

theorem actualHessian_diagonal_translate_add_const (v : E → ℝ) (x y : E) (c : ℝ) :
    actualHessian (fun z => v (z+y-x)+c) x = actualHessian v y := by
  rw [diagonal_translate_eq v x y c,actualHessian_add_const,actualHessian_comp_add_right]
  congr 1
  abel

theorem normalizedPLaplacian_diagonal_translate_add_const
    (p : ℝ) (v : E → ℝ) (x y : E) (c : ℝ) :
    normalizedPLaplacian p (fun z => v (z+y-x)+c) x = normalizedPLaplacian p v y := by
  rw [diagonal_translate_eq v x y c,normalizedPLaplacian_add_const,
    normalizedPLaplacian_comp_add_right]
  congr 1
  abel

theorem classicalPLaplacian_diagonal_translate_add_const
    (p : ℝ) (v : E → ℝ) (x y : E) (c : ℝ) :
    classicalPLaplacian p (fun z => v (z+y-x)+c) x = classicalPLaplacian p v y := by
  unfold classicalPLaplacian
  rw [gradient_diagonal_translate_add_const,normalizedPLaplacian_diagonal_translate_add_const]

end BMCompactAnalytic
#print axioms BMCompactAnalytic.gradient_comp_add_right_actual
#print axioms BMCompactAnalytic.actualHessian_comp_add_right
#print axioms BMCompactAnalytic.actualLaplacian_comp_add_right
#print axioms BMCompactAnalytic.normalizedPLaplacian_comp_add_right
#print axioms BMCompactAnalytic.classicalPLaplacian_comp_add_right
#print axioms BMCompactAnalytic.contDiffAt_diagonal_translate_add_const
#print axioms BMCompactAnalytic.gradient_diagonal_translate_add_const
#print axioms BMCompactAnalytic.actualHessian_diagonal_translate_add_const
#print axioms BMCompactAnalytic.normalizedPLaplacian_diagonal_translate_add_const
#print axioms BMCompactAnalytic.classicalPLaplacian_diagonal_translate_add_const
