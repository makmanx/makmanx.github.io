import BallGreenCore
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact scalar capacity recipes for the proved ball asymptotic constant.
These do not assert a choice-independent capacity assignment for arbitrary sets. -/
noncomputable section
set_option autoImplicit false

namespace BMCompactPDE

theorem ballGreen_capacity_recipe_critical (n : ℕ) {σ R : ℝ}
    (hσ : 0 < σ) (hR : 0 < R) :
    greenCapacityOfConstant n σ (n : ℝ)
      (-fundamentalRadialValue n σ (n : ℝ) R) =
        Real.exp (1 / σ ^ (-((n : ℝ) - 1)⁻¹)) * R := by
  have hγ : 0 < σ ^ (-((n : ℝ) - 1)⁻¹) := Real.rpow_pos_of_pos hσ _
  simp only [greenCapacityOfConstant, if_pos rfl, ite_true, fundamentalRadialValue,
    fundamentalPotential, criticalRadialPotential, Real.norm_eq_abs, abs_of_pos hR]
  have hexp : -(-(σ ^ (-((n : ℝ) - 1)⁻¹) * Real.log R + 1)) /
      σ ^ (-((n : ℝ) - 1)⁻¹) =
        1 / σ ^ (-((n : ℝ) - 1)⁻¹) + Real.log R := by
    field_simp [ne_of_gt hγ]
    ring
  rw [hexp, Real.exp_add, Real.exp_log hR]

theorem ballGreen_capacity_recipe_supercritical (n : ℕ) {σ p R : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) < p) (hσ : 0 < σ) (hR : 0 < R) :
    greenCapacityOfConstant n σ p (-fundamentalRadialValue n σ p R) =
      (((p - (n : ℝ)) / (p - 1))⁻¹) ^ (p - 1) * σ⁻¹ * R ^ (p - (n : ℝ)) := by
  have hden : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (hn.trans hpn))
  have hq : 0 < (p - (n : ℝ)) / (p - 1) :=
    div_pos (sub_pos.mpr hpn) (sub_pos.mpr (hn.trans hpn))
  simp only [greenCapacityOfConstant, if_neg (ne_of_gt hpn), fundamentalRadialValue,
    fundamentalPotential, radialPowerPotential, Real.norm_eq_abs, abs_of_pos hR, neg_neg]
  rw [Real.mul_rpow (mul_nonneg (inv_nonneg.mpr hq.le)
      (Real.rpow_nonneg hσ.le _)) (Real.rpow_nonneg hR.le _),
    Real.mul_rpow (inv_nonneg.mpr hq.le) (Real.rpow_nonneg hσ.le _),
    ← Real.rpow_mul hσ.le, ← Real.rpow_mul hR.le]
  have hσexp : -(p - 1)⁻¹ * (p - 1) = -1 := by field_simp [hden]
  have hRexp : (p - (n : ℝ)) / (p - 1) * (p - 1) = p - (n : ℝ) :=
    div_mul_cancel₀ _ hden
  rw [hσexp, hRexp, Real.rpow_neg_one]

end BMCompactPDE

#print axioms BMCompactPDE.ballGreen_capacity_recipe_critical
#print axioms BMCompactPDE.ballGreen_capacity_recipe_supercritical
