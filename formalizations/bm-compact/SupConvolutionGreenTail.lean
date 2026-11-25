import SupConvolutionRadialTail
import BallGreenOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Specialization of the relative envelope tail to the concrete logarithmic/power
fundamental potential and the existing actual Green-remainder predicate.
Existence of Green functions for general compact sets is not assumed proved.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology

namespace BMCompactPDE

theorem tendsto_fundamentalPotential_atTop (n : ℕ) {σ p : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hσ : 0 < σ) :
    Tendsto (fundamentalPotential n σ p : Space n → ℝ)
      (cobounded (Space n)) atTop := by
  have hnorm : Tendsto (fun x : Space n => ‖x‖) (cobounded (Space n)) atTop :=
    tendsto_norm_cobounded_atTop
  by_cases hp : p = (n : ℝ)
  · subst p
    have hlim := tendsto_atTop_add_const_right (cobounded (Space n)) (1 : ℝ)
      ((Real.tendsto_log_atTop.comp hnorm).const_mul_atTop
        (Real.rpow_pos_of_pos hσ (-((n : ℝ) - 1)⁻¹)))
    exact hlim.congr (fun x => by simp [fundamentalPotential, criticalRadialPotential])
  · have hlt : (n : ℝ) < p := lt_of_le_of_ne hpn (Ne.symm hp)
    have hq : 0 < (p - (n : ℝ)) / (p - 1) :=
      div_pos (sub_pos.mpr hlt) (sub_pos.mpr (hn.trans hlt))
    have hlim := ((tendsto_rpow_atTop hq).comp hnorm).const_mul_atTop
      (mul_pos (inv_pos.mpr hq) (Real.rpow_pos_of_pos hσ (-(p - 1)⁻¹)))
    exact hlim.congr (fun x => by simp [fundamentalPotential, hp, radialPowerPotential])

/-- Printed Lemma4.1(d), critical/supercritical branch, for three actual
functions with bounded Green remainders. The hypotheses are the defined
fundamental-solution asymptotics, not the envelope's desired conclusion. -/
theorem tendsto_negativeGreenEnvelope_add_atBot
    (n : ℕ) {σ p t theta : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (hσ : 0 < σ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hθ0 : 0 ≤ theta) (hθ1 : theta < 1)
    {G₁ G₂ G : Space n → ℝ}
    (hG₁ : HasBoundedGreenRemainder n σ p G₁)
    (hG₂ : HasBoundedGreenRemainder n σ p G₂)
    (hG : HasBoundedGreenRemainder n σ p G) :
    Tendsto (fun x => BMCompactEnvelope.supConvolution t
      (fun y => -G₁ y) (fun z => -G₂ z) x + theta * G x)
      (cobounded (Space n)) atBot := by
  obtain ⟨C₁,hC₁,h₁⟩ := hG₁
  obtain ⟨C₂,hC₂,h₂⟩ := hG₂
  obtain ⟨C₃,hC₃,h₃⟩ := hG
  let C := max C₁ (max C₂ C₃)
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  have hC1 : C₁ ≤ C := le_max_left _ _
  have hC2 : C₂ ≤ C := (le_max_left C₂ C₃).trans (le_max_right C₁ (max C₂ C₃))
  have hC3 : C₃ ≤ C := (le_max_right C₂ C₃).trans (le_max_right C₁ (max C₂ C₃))
  have hall : ∀ᶠ x in cobounded (Space n),
      |G₁ x - fundamentalPotential n σ p x| ≤ C ∧
      |G₂ x - fundamentalPotential n σ p x| ≤ C ∧
      |G x - fundamentalPotential n σ p x| ≤ C := by
    filter_upwards [h₁,h₂,h₃] with x hx₁ hx₂ hx₃
    exact ⟨hx₁.trans hC1,hx₂.trans hC2,hx₃.trans hC3⟩
  obtain ⟨R,_,hR⟩ := hasBasis_cobounded_norm.eventually_iff.mp hall
  let S := max R 1
  have hmono : ∀ {x y : Space n}, S ≤ ‖x‖ → ‖x‖ ≤ ‖y‖ →
      fundamentalPotential n σ p x ≤ fundamentalPotential n σ p y := by
    intro x y hx hxy
    rw [← fundamentalPotential_norm n σ p x, ← fundamentalPotential_norm n σ p y]
    exact fundamentalRadialValue_mono_positive n hn hpn hσ
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((le_max_right _ _).trans hx)) hxy
  have htail : ∀ x : Space n, S ≤ ‖x‖ →
      |G₁ x - fundamentalPotential n σ p x| ≤ C ∧
      |G₂ x - fundamentalPotential n σ p x| ≤ C ∧
      |G x - fundamentalPotential n σ p x| ≤ C := by
    intro x hx
    exact hR ((le_max_left _ _).trans hx)
  have hlim := BMCompactEnvelope.tendsto_supConvolution_sub_smul_atBot
    ht0 ht1 hC hθ0 hθ1 hmono (tendsto_fundamentalPotential_atTop n hn hpn hσ)
    (u := fun y => -G₁ y) (v := fun z => -G₂ z) (w := fun x => -G x)
    (fun x hx => by linarith [(abs_le.mp (htail x hx).1).1])
    (fun x hx => by linarith [(abs_le.mp (htail x hx).2.1).1])
    (fun x hx => by linarith [(abs_le.mp (htail x hx).2.2).2])
  simpa only [mul_neg, sub_neg_eq_add] using hlim

end BMCompactPDE

#print axioms BMCompactPDE.tendsto_fundamentalPotential_atTop
#print axioms BMCompactPDE.tendsto_negativeGreenEnvelope_add_atBot
