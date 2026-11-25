import RadialDivergenceCore
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
set_option autoImplicit false
open InnerProductSpace
open scoped InnerProductSpace

namespace BMCompactPDE

theorem classicalDivergence_eq_sum_fderiv_coordinates {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    classicalDivergence F x = ∑ i : Fin n,
      (fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ i)) i := by
  unfold classicalDivergence
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  simp [Matrix.trace, LinearMap.toMatrix_apply]

/-- Compatibility between the trace definition and the coordinate expression
used by the compact-support integration-by-parts argument. -/
theorem classicalDivergence_eq_sum_gradient_coordinates {n : ℕ}
    {F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hF : DifferentiableAt ℝ F x) :
    classicalDivergence F x = ∑ i : Fin n,
      (gradient (fun y => F y i) x) i := by
  rw [classicalDivergence_eq_sum_fderiv_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  have hi : HasFDerivAt (fun y => F y i)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).comp (fderiv ℝ F x)) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).hasFDerivAt.comp x hF.hasFDerivAt
  calc
    (fderiv ℝ F x (EuclideanSpace.basisFun (Fin n) ℝ i)) i =
        fderiv ℝ (fun y => F y i) x (EuclideanSpace.basisFun (Fin n) ℝ i) := by
          rw [hi.fderiv]
          rfl
    _ = (gradient (fun y => F y i) x) i := by
      rw [← inner_gradient_left, EuclideanSpace.inner_basisFun_real]

end BMCompactPDE

#print axioms BMCompactPDE.classicalDivergence_eq_sum_fderiv_coordinates
#print axioms BMCompactPDE.classicalDivergence_eq_sum_gradient_coordinates
