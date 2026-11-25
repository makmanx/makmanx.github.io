import RadialFoundation

/-!
Concrete radial profiles from source label eqn2.7. The parameter σ is a positive
normalization constant; its identification with the surface area of the unit
sphere, and the distributional point-source identity, are separate obligations.
No p-harmonicity, existence of a Green function, or main inequality is assumed.
-/

noncomputable section
set_option autoImplicit false
open InnerProductSpace
open scoped InnerProductSpace

namespace BMCompactPDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def radialPowerProfile (a q : ℝ) (x : E) : ℝ := a * ‖x‖ ^ q

def radialPowerPotential (n : ℕ) (σ p : ℝ) (x : E) : ℝ :=
  (((p - (n : ℝ)) / (p - 1))⁻¹ * σ ^ (-(p - 1)⁻¹)) *
    ‖x‖ ^ ((p - (n : ℝ)) / (p - 1))

def criticalRadialPotential (n : ℕ) (σ : ℝ) (x : E) : ℝ :=
  σ ^ (-((n : ℝ) - 1)⁻¹) * Real.log ‖x‖ + 1

def fundamentalPotential (n : ℕ) (σ p : ℝ) (x : E) : ℝ :=
  if p = (n : ℝ) then criticalRadialPotential n σ x else radialPowerPotential n σ p x

def normalizedRadialGradient (n : ℕ) (σ p : ℝ) (x : E) : E :=
  (σ ^ (-(p - 1)⁻¹) * ‖x‖ ^ ((p - (n : ℝ)) / (p - 1) - 2)) • x

theorem fundamentalPotential_zero_of_supercritical (n : ℕ) (σ : ℝ) {p : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) < p) :
    fundamentalPotential n σ p (0 : E) = 0 := by
  have hpne : p ≠ (n : ℝ) := ne_of_gt hpn
  have hq : 0 < (p - (n : ℝ)) / (p - 1) :=
    div_pos (sub_pos.mpr hpn) (sub_pos.mpr (hn.trans hpn))
  simp [fundamentalPotential, hpne, radialPowerPotential, Real.zero_rpow hq.ne']

theorem normalizedRadialGradient_ne_zero (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) {x : E} (hx : x ≠ 0) :
    normalizedRadialGradient n σ p x ≠ 0 := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  exact smul_ne_zero
    (mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hσ _))
      (ne_of_gt (Real.rpow_pos_of_pos hr _))) hx

theorem pFlux_normalizedRadialGradient (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hp : 1 < p) {x : E} (hx : x ≠ 0) :
    pFlux p (normalizedRadialGradient n σ p x) =
      (σ⁻¹ * ‖x‖ ^ (-(n : ℝ))) • x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hden : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hcoeff : 0 ≤ σ ^ (-(p - 1)⁻¹) *
      ‖x‖ ^ ((p - (n : ℝ)) / (p - 1) - 2) :=
    mul_nonneg (Real.rpow_nonneg hσ.le _) (Real.rpow_nonneg hr.le _)
  unfold normalizedRadialGradient
  rw [pFlux_nonneg_smul hp hcoeff, pFlux, smul_smul]
  congr 1
  rw [Real.mul_rpow (Real.rpow_nonneg hσ.le _) (Real.rpow_nonneg hr.le _),
    ← Real.rpow_mul hσ.le, ← Real.rpow_mul hr.le]
  rw [mul_assoc, ← Real.rpow_add hr]
  have hσexp : -(p - 1)⁻¹ * (p - 1) = -1 := by field_simp [hden]
  have hrexp : ((p - (n : ℝ)) / (p - 1) - 2) * (p - 1) + (p - 2) =
      -(n : ℝ) := by
    field_simp [hden]
    ring
  rw [hσexp, hrexp, Real.rpow_neg_one]

section Complete
variable [CompleteSpace E]

theorem hasGradientAt_scalar_norm_rpow (a q : ℝ) {x : E} (hx : x ≠ 0) :
    HasGradientAt (radialPowerProfile a q : E → ℝ)
      ((a * q * ‖x‖ ^ (q - 2)) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlin : toDual ℝ E ((a * q * ‖x‖ ^ (q - 2)) • x) =
      a • ((q * ‖x‖ ^ (q - 2)) • innerSL ℝ x) := by
    ext y
    simp [real_inner_smul_left, mul_assoc]
  rw [hlin]
  exact (hasFDerivAt_norm_rpow_nonzero q hx).const_mul a

theorem hasGradientAt_radialPowerPotential (n : ℕ) {σ p : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) < p) {x : E} (hx : x ≠ 0) :
    HasGradientAt (radialPowerPotential n σ p : E → ℝ)
      (normalizedRadialGradient n σ p x) x := by
  let q := (p - (n : ℝ)) / (p - 1)
  let c := σ ^ (-(p - 1)⁻¹)
  have hq : q ≠ 0 := ne_of_gt (div_pos (sub_pos.mpr hpn)
    (sub_pos.mpr (hn.trans hpn)))
  have hscale : (q⁻¹ * c) * q = c := by field_simp [hq]
  have h := hasGradientAt_scalar_norm_rpow (q⁻¹ * c) q hx
  rw [hscale] at h
  exact h

theorem hasGradientAt_log_norm {x : E} (hx : x ≠ 0) :
    HasGradientAt (fun y : E => Real.log ‖y‖) (‖x‖ ^ (-2 : ℝ) • x) x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm : HasFDerivAt (fun y : E => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
    simpa only [Real.rpow_one, one_mul, show (1 : ℝ) - 2 = -1 by norm_num,
      Real.rpow_neg_one] using hasFDerivAt_norm_rpow_nonzero (E := E) 1 hx
  have hlog := hnorm.log (ne_of_gt hr)
  have hexp : ‖x‖ ^ (-2 : ℝ) = ‖x‖⁻¹ * ‖x‖⁻¹ := by
    rw [show (-2 : ℝ) = -1 + -1 by ring, Real.rpow_add hr, Real.rpow_neg_one]
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlin : toDual ℝ E (‖x‖ ^ (-2 : ℝ) • x) =
      ‖x‖⁻¹ • (‖x‖⁻¹ • innerSL ℝ x) := by
    ext y
    simp [hexp, real_inner_smul_left, mul_assoc]
  rw [hlin]
  exact hlog

theorem hasGradientAt_criticalRadialPotential (n : ℕ) (σ : ℝ) {x : E} (hx : x ≠ 0) :
    HasGradientAt (criticalRadialPotential n σ : E → ℝ)
      (normalizedRadialGradient n σ (n : ℝ) x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlog := (hasGradientAt_log_norm hx).hasFDerivAt
  have h := (hlog.const_mul (σ ^ (-((n : ℝ) - 1)⁻¹))).add_const 1
  have hlin : toDual ℝ E (normalizedRadialGradient n σ (n : ℝ) x) =
      σ ^ (-((n : ℝ) - 1)⁻¹) • toDual ℝ E (‖x‖ ^ (-2 : ℝ) • x) := by
    ext y
    simp [normalizedRadialGradient, real_inner_smul_left, mul_assoc]
  rw [hlin]
  exact h

theorem hasGradientAt_fundamentalPotential (n : ℕ) {σ p : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) {x : E} (hx : x ≠ 0) :
    HasGradientAt (fundamentalPotential n σ p : E → ℝ)
      (normalizedRadialGradient n σ p x) x := by
  by_cases h : p = (n : ℝ)
  · subst p
    have hf : (fundamentalPotential n σ (n : ℝ) : E → ℝ) =
        criticalRadialPotential n σ := by
      funext y
      simp [fundamentalPotential]
    rw [hf]
    exact hasGradientAt_criticalRadialPotential n σ hx
  · have hlt : (n : ℝ) < p := lt_of_le_of_ne hpn (Ne.symm h)
    have hf : (fundamentalPotential n σ p : E → ℝ) =
        radialPowerPotential n σ p := by
      funext y
      simp [fundamentalPotential, h]
    rw [hf]
    exact hasGradientAt_radialPowerPotential n hn hlt hx

/-- The pointwise flux formula in the text after source label eqn2.7.
The point-source distributional equation is not asserted here. -/
theorem pFlux_gradient_fundamentalPotential (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p)
    {x : E} (hx : x ≠ 0) :
    pFlux p (gradient (fundamentalPotential n σ p : E → ℝ) x) =
      (σ⁻¹ * ‖x‖ ^ (-(n : ℝ))) • x := by
  rw [(hasGradientAt_fundamentalPotential n hn hpn hx).gradient]
  exact pFlux_normalizedRadialGradient n hσ (lt_of_lt_of_le hn hpn) hx

end Complete

end BMCompactPDE

#print axioms BMCompactPDE.pFlux_normalizedRadialGradient
#print axioms BMCompactPDE.hasGradientAt_fundamentalPotential
#print axioms BMCompactPDE.pFlux_gradient_fundamentalPotential
