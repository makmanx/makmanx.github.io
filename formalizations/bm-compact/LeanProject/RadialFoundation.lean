import GreenFoundation
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
open InnerProductSpace

namespace BMCompactPDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact first variation of the p-energy density. -/
theorem hasFDerivAt_energy_norm {p : ℝ} (hp : 1 < p) (x : E) :
    HasFDerivAt (fun y : E => ‖y‖ ^ p)
      ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) x :=
  hasFDerivAt_norm_rpow x hp

theorem hasFDerivAt_norm_rpow_nonzero (q : ℝ) {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E => ‖y‖ ^ q)
      ((q * ‖x‖ ^ (q - 2)) • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
    (p := q / 2) (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))
  convert h using 1
  · funext y
    rw [← Real.rpow_natCast_mul (norm_nonneg y) 2]
    congr 1
    ring
  · have hpow : (‖x‖ ^ 2) ^ (q / 2 - 1) = ‖x‖ ^ (q - 2) := by
      rw [← Real.rpow_natCast_mul (norm_nonneg x) 2]
      congr 1
      ring
    apply ContinuousLinearMap.ext
    intro y
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
      nsmul_eq_mul, hpow]
    ring

section Complete
variable [CompleteSpace E]

theorem hasGradientAt_energy_norm {p : ℝ} (hp : 1 < p) (x : E) :
    HasGradientAt (fun y : E => ‖y‖ ^ p) (p • pFlux p x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlin : toDual ℝ E (p • pFlux p x) =
      (p * ‖x‖ ^ (p - 2)) • innerSL ℝ x := by
    ext y
    simp [pFlux, real_inner_smul_left, mul_assoc]
  rw [hlin]
  exact hasFDerivAt_energy_norm hp x

theorem gradient_energy_norm {p : ℝ} (hp : 1 < p) (x : E) :
    gradient (fun y : E => ‖y‖ ^ p) x = p • pFlux p x :=
  (hasGradientAt_energy_norm hp x).gradient

end Complete

end BMCompactPDE

#print axioms BMCompactPDE.hasFDerivAt_norm_rpow_nonzero
#print axioms BMCompactPDE.hasGradientAt_energy_norm
#print axioms BMCompactPDE.gradient_energy_norm
