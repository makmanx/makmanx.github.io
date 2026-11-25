import GreenDefs
import Mathlib.Tactic.Ring

/-! Exact normalization-profile dilation identities needed in Green homogeneity.
They do not assert dilation invariance of arbitrary weak PDE solutions or a
choice-independent Green capacity. The normalization σ remains explicit. -/
noncomputable section
set_option autoImplicit false

namespace BMCompactPDE

theorem fundamentalPotential_dilate_critical (n : ℕ) (σ : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) {x : Space n} (hx : x ≠ 0) :
    fundamentalPotential n σ (n : ℝ) (ρ • x) =
      fundamentalPotential n σ (n : ℝ) x +
        σ ^ (-((n : ℝ) - 1)⁻¹) * Real.log ρ := by
  simp only [fundamentalPotential, ite_true, criticalRadialPotential,
    norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  rw [Real.log_mul (ne_of_gt hρ) (norm_ne_zero_iff.mpr hx)]
  ring

theorem fundamentalPotential_dilate_supercritical (n : ℕ) (σ : ℝ) {p ρ : ℝ}
    (hpn : (n : ℝ) < p) (hρ : 0 < ρ) (x : Space n) :
    fundamentalPotential n σ p (ρ • x) =
      ρ ^ ((p - (n : ℝ)) / (p - 1)) * fundamentalPotential n σ p x := by
  simp only [fundamentalPotential, if_neg (ne_of_gt hpn), radialPowerPotential,
    norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  rw [Real.mul_rpow hρ.le (norm_nonneg x)]
  ring

end BMCompactPDE

#print axioms BMCompactPDE.fundamentalPotential_dilate_critical
#print axioms BMCompactPDE.fundamentalPotential_dilate_supercritical
