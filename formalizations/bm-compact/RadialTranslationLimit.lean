import GreenDefs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual vanishing change of the radial normalization under translation.
This is an analytic theorem, not an assumed translation law for Green capacity. -/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology

namespace BMCompactPDE

theorem rpow_tail_lipschitz {q T r s : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hT : 0 < T) (hr : T ≤ r) (hs : T ≤ s) :
    ‖s ^ q - r ^ q‖ ≤ (q * T ^ (q - 1)) * ‖s - r‖ := by
  have hd : ∀ t ∈ Ici T, HasDerivWithinAt (fun z : ℝ => z ^ q)
      (q * t ^ (q - 1)) (Ici T) t := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hT.trans_le ht)))).hasDerivWithinAt
  have hb : ∀ t ∈ Ici T, ‖q * t ^ (q - 1)‖ ≤ q * T ^ (q - 1) := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hq0 (Real.rpow_nonneg
      (hT.trans_le ht).le _))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hT ht (sub_nonpos.mpr hq1)) hq0
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Ici T) hr hs

theorem abs_norm_translate_sub_norm_le {n : ℕ} (x a : Space n) :
    |‖x - a‖ - ‖x‖| ≤ ‖a‖ := by
  have h := abs_norm_sub_norm_le (x - a) x
  have halg : (x - a) - x = -a := by rw [sub_right_comm, sub_self, zero_sub]
  simpa only [halg, norm_neg] using h

theorem tendsto_norm_rpow_translate_sub {n : ℕ} {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (a : Space n) :
    Tendsto (fun x : Space n => ‖x - a‖ ^ q - ‖x‖ ^ q)
      (cobounded (Space n)) (nhds 0) := by
  have htop : Tendsto (fun x : Space n => ‖x‖) (cobounded (Space n)) atTop := by
    simpa using Metric.tendsto_dist_right_cobounded_atTop (0 : Space n)
  have hpow : Tendsto (fun x : Space n => (‖x‖ - ‖a‖) ^ (q - 1))
      (cobounded (Space n)) (nhds 0) := by
    have hshift : Tendsto (fun x : Space n => ‖x‖ - ‖a‖) (cobounded (Space n)) atTop := by
      simpa only [sub_eq_add_neg] using
        tendsto_atTop_add_const_right (cobounded (Space n)) (-‖a‖) htop
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hq1)).comp hshift
    have he : -(1 - q) = q - 1 := by ring
    simpa only [he, Function.comp_def] using h
  have hlim : Tendsto (fun x : Space n => (q * (‖x‖ - ‖a‖) ^ (q - 1)) * ‖a‖)
      (cobounded (Space n)) (nhds 0) := by
    simpa only [mul_zero, zero_mul] using (hpow.const_mul q).mul_const ‖a‖
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_const_nhds.squeeze' hlim (Eventually.of_forall (fun x => norm_nonneg _))
  filter_upwards [htop.eventually (eventually_gt_atTop ‖a‖)] with x hx
  have hT : 0 < ‖x‖ - ‖a‖ := sub_pos.mpr hx
  have hbd := abs_norm_translate_sub_norm_le x a
  have hs : ‖x‖ - ‖a‖ ≤ ‖x - a‖ := by linarith [(abs_le.mp hbd).1]
  have hr : ‖x‖ - ‖a‖ ≤ ‖x‖ := sub_le_self _ (norm_nonneg a)
  have hp := rpow_tail_lipschitz hq0.le hq1.le hT hr hs
  have hdist : ‖‖x - a‖ - ‖x‖‖ ≤ ‖a‖ := by simpa only [Real.norm_eq_abs] using hbd
  exact hp.trans (mul_le_mul_of_nonneg_left hdist
    (mul_nonneg hq0.le (Real.rpow_nonneg hT.le _)))

theorem tendsto_log_norm_translate_sub {n : ℕ} (a : Space n) :
    Tendsto (fun x : Space n => Real.log ‖x - a‖ - Real.log ‖x‖)
      (cobounded (Space n)) (nhds 0) := by
  have htop : Tendsto (fun x : Space n => ‖x‖) (cobounded (Space n)) atTop := by
    simpa using Metric.tendsto_dist_right_cobounded_atTop (0 : Space n)
  have hlo := (Real.tendsto_log_comp_add_sub_log (-‖a‖)).comp htop
  have hhi := (Real.tendsto_log_comp_add_sub_log ‖a‖).comp htop
  apply hlo.squeeze' hhi
  · filter_upwards [htop.eventually (eventually_gt_atTop ‖a‖)] with x hx
    have hbd := abs_norm_translate_sub_norm_le x a
    have hs : ‖x‖ - ‖a‖ ≤ ‖x - a‖ := by linarith [(abs_le.mp hbd).1]
    simpa only [sub_eq_add_neg, Function.comp_apply] using
      sub_le_sub_right (Real.log_le_log (sub_pos.mpr hx) hs) (Real.log ‖x‖)
  · filter_upwards [htop.eventually (eventually_gt_atTop ‖a‖)] with x hx
    have hbd := abs_norm_translate_sub_norm_le x a
    have hs : ‖x - a‖ ≤ ‖x‖ + ‖a‖ := by linarith [(abs_le.mp hbd).2]
    have hpos : 0 < ‖x - a‖ := by linarith [(abs_le.mp hbd).1]
    exact sub_le_sub_right (Real.log_le_log hpos hs) (Real.log ‖x‖)

theorem tendsto_fundamentalPotential_translate_sub (n : ℕ) (σ : ℝ) {p : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (a : Space n) :
    Tendsto (fun x : Space n => fundamentalPotential n σ p (x - a) -
      fundamentalPotential n σ p x) (cobounded (Space n)) (nhds 0) := by
  by_cases hp : p = (n : ℝ)
  · subst p
    have heq : (fun x : Space n => fundamentalPotential n σ (n : ℝ) (x - a) -
        fundamentalPotential n σ (n : ℝ) x) =
        (fun x => σ ^ (-((n : ℝ) - 1)⁻¹) * (Real.log ‖x - a‖ - Real.log ‖x‖)) := by
      funext x
      simp only [fundamentalPotential, if_pos rfl, ite_true, criticalRadialPotential]
      ring
    rw [heq]
    simpa only [mul_zero] using (tendsto_log_norm_translate_sub a).const_mul
      (σ ^ (-((n : ℝ) - 1)⁻¹))
  · have hlt : (n : ℝ) < p := lt_of_le_of_ne hpn (Ne.symm hp)
    have hden : 0 < p - 1 := sub_pos.mpr (hn.trans hlt)
    have hq0 : 0 < (p - (n : ℝ)) / (p - 1) := div_pos (sub_pos.mpr hlt) hden
    have hq1 : (p - (n : ℝ)) / (p - 1) < 1 := by
      rw [div_lt_one hden]
      linarith
    have heq : (fun x : Space n => fundamentalPotential n σ p (x - a) -
        fundamentalPotential n σ p x) =
        (fun x => (((p - (n : ℝ)) / (p - 1))⁻¹ * σ ^ (-(p - 1)⁻¹)) *
          (‖x - a‖ ^ ((p - (n : ℝ)) / (p - 1)) - ‖x‖ ^ ((p - (n : ℝ)) / (p - 1)))) := by
      funext x
      simp only [fundamentalPotential, if_neg hp, radialPowerPotential]
      ring
    rw [heq]
    simpa only [mul_zero] using (tendsto_norm_rpow_translate_sub hq0 hq1 a).const_mul
      ((((p - (n : ℝ)) / (p - 1))⁻¹ * σ ^ (-(p - 1)⁻¹)))

end BMCompactPDE

#print axioms BMCompactPDE.rpow_tail_lipschitz
#print axioms BMCompactPDE.abs_norm_translate_sub_norm_le
#print axioms BMCompactPDE.tendsto_norm_rpow_translate_sub
#print axioms BMCompactPDE.tendsto_log_norm_translate_sub
#print axioms BMCompactPDE.tendsto_fundamentalPotential_translate_sub
