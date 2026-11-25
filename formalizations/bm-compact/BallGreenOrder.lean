import BallGreenCore

/-! Positivity and radial ordering for the actual explicit ball Green candidate. -/
noncomputable section
set_option autoImplicit false

namespace BMCompactPDE

theorem strictMonoOn_fundamentalRadialValue (n : ℕ) {σ p : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hσ : 0 < σ) :
    StrictMonoOn (fundamentalRadialValue n σ p) (Set.Ioi 0) := by
  intro r hr s hs hrs
  change 0 < r at hr
  change 0 < s at hs
  by_cases hp : p = (n : ℝ)
  · subst p
    simp only [fundamentalRadialValue, fundamentalPotential, if_pos rfl, ite_true,
      criticalRadialPotential, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hs]
    have hmul := mul_lt_mul_of_pos_left (Real.log_lt_log hr hrs)
      (Real.rpow_pos_of_pos hσ (-((n : ℝ) - 1)⁻¹))
    linarith

  · have hlt : (n : ℝ) < p := lt_of_le_of_ne hpn (Ne.symm hp)
    have hq : 0 < (p - (n : ℝ)) / (p - 1) :=
      div_pos (sub_pos.mpr hlt) (sub_pos.mpr (hn.trans hlt))
    simp only [fundamentalRadialValue, fundamentalPotential, if_neg hp,
      radialPowerPotential, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hs]
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hr.le hrs hq)
      (mul_pos (inv_pos.mpr hq) (Real.rpow_pos_of_pos hσ _))

theorem fundamentalRadialValue_mono_positive (n : ℕ) {σ p r s : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hσ : 0 < σ)
    (hr : 0 < r) (hrs : r ≤ s) :
    fundamentalRadialValue n σ p r ≤ fundamentalRadialValue n σ p s :=
  (strictMonoOn_fundamentalRadialValue n hn hpn hσ).monotoneOn hr (hr.trans_le hrs) hrs

theorem ballGreen_nonneg (n : ℕ) {σ p R : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hσ : 0 < σ)
    (hR : 0 < R) (x : Space n) : 0 ≤ ballGreen n σ p R x := by
  exact sub_nonneg.mpr
    (fundamentalRadialValue_mono_positive n hn hpn hσ hR (le_max_left _ _))

theorem ballGreen_pos_of_lt_norm (n : ℕ) {σ p R : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hσ : 0 < σ)
    (hR : 0 < R) {x : Space n} (hx : R < ‖x‖) :
    0 < ballGreen n σ p R x := by
  change 0 < fundamentalRadialValue n σ p (max R ‖x‖) - fundamentalRadialValue n σ p R
  rw [max_eq_right hx.le]
  exact sub_pos.mpr ((strictMonoOn_fundamentalRadialValue n hn hpn hσ)
    hR (hR.trans hx) hx)

theorem ballGreen_eq_zero_iff_norm_le (n : ℕ) {σ p R : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hσ : 0 < σ)
    (hR : 0 < R) (x : Space n) :
    ballGreen n σ p R x = 0 ↔ ‖x‖ ≤ R := by
  constructor
  · intro hz
    by_contra h
    have hp := ballGreen_pos_of_lt_norm n hn hpn hσ hR (lt_of_not_ge h)
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · exact ballGreen_eq_zero_of_norm_le n σ p R

end BMCompactPDE

#print axioms BMCompactPDE.strictMonoOn_fundamentalRadialValue
#print axioms BMCompactPDE.fundamentalRadialValue_mono_positive
#print axioms BMCompactPDE.ballGreen_nonneg
#print axioms BMCompactPDE.ballGreen_pos_of_lt_norm
#print axioms BMCompactPDE.ballGreen_eq_zero_iff_norm_le
