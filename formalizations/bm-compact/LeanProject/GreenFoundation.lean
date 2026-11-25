import FluxDefs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
Concrete algebraic foundations of the nonlinear p-Laplace flux in the manuscript.
These results do not assume any p-harmonicity or capacitary inequality.
The strict monotonicity theorem is the pointwise coercive fact required in weak
comparison arguments; the dual-power identity supplies the flux integrability
exponent once a weak gradient is in L^p.
-/

noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
open Filter Topology

namespace BMCompactPDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem rpow_coefficient_mul {p r : ℝ} (hp : 1 < p) (hr : 0 ≤ r) :
    r ^ (p - 2) * r = r ^ (p - 1) := by
  rw [← Real.rpow_add_one' hr (by linarith : p - 2 + 1 ≠ 0)]
  congr 1
  ring

theorem norm_pFlux {p : ℝ} (hp : 1 < p) (v : E) :
    ‖pFlux p v‖ = ‖v‖ ^ (p - 1) := by
  simp only [pFlux, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg v) (p - 2))]
  exact rpow_coefficient_mul hp (norm_nonneg v)

theorem pFlux_inner_self {p : ℝ} (hp : 1 < p) (v : E) :
    ⟪pFlux p v, v⟫_ℝ = ‖v‖ ^ p := by
  rw [pFlux, real_inner_smul_left, real_inner_self_eq_norm_mul_norm,
    ← mul_assoc, rpow_coefficient_mul hp (norm_nonneg v)]
  rw [← Real.rpow_add_one' (norm_nonneg v) (by linarith : p - 1 + 1 ≠ 0)]
  congr 1
  ring

theorem pFlux_smul (p a : ℝ) (v : E) :
    pFlux p (a • v) = (|a| ^ (p - 2) * a) • pFlux p v := by
  simp only [pFlux, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg a) (norm_nonneg v), smul_smul]
  congr 1
  ring

theorem pFlux_nonneg_smul {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (v : E) :
    pFlux p (a • v) = a ^ (p - 1) • pFlux p v := by
  rw [pFlux_smul, abs_of_nonneg ha, rpow_coefficient_mul hp ha]

theorem pFlux_pairing_lower_bound {p : ℝ} (hp : 1 < p) (v w : E) :
    (‖v‖ ^ (p - 1) - ‖w‖ ^ (p - 1)) * (‖v‖ - ‖w‖) ≤
      ⟪pFlux p v - pFlux p w, v - w⟫_ℝ := by
  let a := ‖v‖ ^ (p - 2)
  let b := ‖w‖ ^ (p - 2)
  have ha : 0 ≤ a := Real.rpow_nonneg (norm_nonneg v) _
  have hb : 0 ≤ b := Real.rpow_nonneg (norm_nonneg w) _
  have hvr : ‖v‖ ^ (p - 1) = a * ‖v‖ :=
    (rpow_coefficient_mul hp (norm_nonneg v)).symm
  have hwr : ‖w‖ ^ (p - 1) = b * ‖w‖ :=
    (rpow_coefficient_mul hp (norm_nonneg w)).symm
  calc
    (‖v‖ ^ (p - 1) - ‖w‖ ^ (p - 1)) * (‖v‖ - ‖w‖) =
        a * ‖v‖ * ‖v‖ + b * ‖w‖ * ‖w‖ - (a + b) * (‖v‖ * ‖w‖) := by
          rw [hvr, hwr]
          ring
    _ ≤ a * ‖v‖ * ‖v‖ + b * ‖w‖ * ‖w‖ - (a + b) * ⟪v, w⟫_ℝ :=
      sub_le_sub_left
        (mul_le_mul_of_nonneg_left (real_inner_le_norm v w) (add_nonneg ha hb)) _
    _ = ⟪pFlux p v - pFlux p w, v - w⟫_ℝ := by
      dsimp only [a, b]
      simp only [pFlux, inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_self_eq_norm_mul_norm, real_inner_comm w v]
      ring

theorem pFlux_strict_monotonicity {p : ℝ} (hp : 1 < p) {v w : E}
    (hvw : v ≠ w) : 0 < ⟪pFlux p v - pFlux p w, v - w⟫_ℝ := by
  by_cases hn : ‖v‖ = ‖w‖
  · have hw : w ≠ 0 := by
      intro hw
      have hv : v = 0 := norm_eq_zero.mp (by simpa [hw] using hn)
      exact hvw (hv.trans hw.symm)
    have hcoeff : 0 < ‖w‖ ^ (p - 2) :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr hw) _
    have hdiff : 0 < ‖v - w‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hvw)) 2
    simp only [pFlux, hn]
    rw [← smul_sub, real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact mul_pos hcoeff hdiff
  · have hprod : 0 <
        (‖v‖ ^ (p - 1) - ‖w‖ ^ (p - 1)) * (‖v‖ - ‖w‖) := by
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact mul_pos_of_neg_of_neg
          (sub_neg.mpr (Real.rpow_lt_rpow (norm_nonneg v) hlt (sub_pos.mpr hp)))
          (sub_neg.mpr hlt)
      · exact mul_pos
          (sub_pos.mpr (Real.rpow_lt_rpow (norm_nonneg w) hgt (sub_pos.mpr hp)))
          (sub_pos.mpr hgt)
    exact lt_of_lt_of_le hprod (pFlux_pairing_lower_bound hp v w)

theorem pFlux_monotonicity {p : ℝ} (hp : 1 < p) (v w : E) :
    0 ≤ ⟪pFlux p v - pFlux p w, v - w⟫_ℝ := by
  by_cases h : v = w
  · simp [h]
  · exact (pFlux_strict_monotonicity hp h).le

theorem pFlux_injective {p : ℝ} (hp : 1 < p) :
    Function.Injective (pFlux p : E → E) := by
  intro v w h
  by_contra hvw
  have hpositive := pFlux_strict_monotonicity hp hvw
  simpa [h] using hpositive

theorem pFlux_eq_zero_iff {p : ℝ} (hp : 1 < p) (v : E) :
    pFlux p v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply pFlux_injective hp
    simpa using h
  · rintro rfl
    exact pFlux_zero p

theorem pFlux_pairing_eq_zero_iff {p : ℝ} (hp : 1 < p) (v w : E) :
    ⟪pFlux p v - pFlux p w, v - w⟫_ℝ = 0 ↔ v = w := by
  constructor
  · intro hzero
    by_contra hvw
    have hpositive := pFlux_strict_monotonicity hp hvw
    rw [hzero] at hpositive
    exact (lt_irrefl 0) hpositive
  · rintro rfl
    simp

theorem norm_pFlux_dual_power {p : ℝ} (hp : 1 < p) (v : E) :
    ‖pFlux p v‖ ^ (p / (p - 1)) = ‖v‖ ^ p := by
  rw [norm_pFlux hp, ← Real.rpow_mul (norm_nonneg v)]
  congr 1
  field_simp [ne_of_gt (sub_pos.mpr hp)]

theorem continuous_pFlux {p : ℝ} (hp : 1 < p) :
    Continuous (pFlux p : E → E) := by
  rw [continuous_iff_continuousAt]
  intro v
  by_cases hv : v = 0
  · subst v
    rw [ContinuousAt, pFlux_zero, tendsto_zero_iff_norm_tendsto_zero]
    have hcont : ContinuousAt (fun w : E => ‖w‖ ^ (p - 1)) 0 :=
      continuous_norm.continuousAt.rpow_const (Or.inr (sub_nonneg.mpr hp.le))
    simpa only [norm_pFlux hp, norm_zero, Real.zero_rpow (ne_of_gt (sub_pos.mpr hp))]
      using hcont.tendsto
  · change ContinuousAt (fun w : E => ‖w‖ ^ (p - 2) • w) v
    exact (continuous_norm.continuousAt.rpow_const
      (Or.inl (norm_ne_zero_iff.mpr hv))).smul continuousAt_id

end BMCompactPDE

#print axioms BMCompactPDE.pFlux_strict_monotonicity
#print axioms BMCompactPDE.pFlux_monotonicity
#print axioms BMCompactPDE.pFlux_inner_self
#print axioms BMCompactPDE.pFlux_nonneg_smul
#print axioms BMCompactPDE.norm_pFlux_dual_power
#print axioms BMCompactPDE.continuous_pFlux
