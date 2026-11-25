import SmoothWeakBridge
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.Linarith

/-! Genuine flat smooth approximants of the scalar positive part. Their slopes
vanish at zero, so the eventual gradient limit at a zero level requires no
unproved assertion about the gradient on that level. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace BMCompactPDE

def smoothPositivePart (j : ℕ) (t : ℝ) : ℝ :=
  t * Real.smoothTransition (((j : ℝ) + 1) * t)

def positivePartSlope (j : ℕ) (t : ℝ) : ℝ :=
  Real.smoothTransition (((j : ℝ) + 1) * t) +
    (((j : ℝ) + 1) * t) * deriv Real.smoothTransition (((j : ℝ) + 1) * t)

theorem deriv_smoothTransition_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Eventually.of_forall (fun x => by
    rw [Real.smoothTransition.zero_of_nonpos ht]
    exact Real.smoothTransition.nonneg x)

theorem deriv_smoothTransition_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMax.deriv_eq_zero
  exact Eventually.of_forall (fun x => by
    rw [Real.smoothTransition.one_of_one_le ht]
    exact Real.smoothTransition.le_one x)

theorem smoothPositivePart_contDiff (j : ℕ) : ContDiff ℝ ∞ (smoothPositivePart j) := by
  exact contDiff_id.mul ((Real.smoothTransition.contDiff :
    ContDiff ℝ ∞ Real.smoothTransition).comp (contDiff_const.mul contDiff_id))

theorem smoothPositivePart_hasDerivAt (j : ℕ) (t : ℝ) :
    HasDerivAt (smoothPositivePart j) (positivePartSlope j t) t := by
  have hm : HasDerivAt (fun s : ℝ => ((j : ℝ) + 1) * s) ((j : ℝ) + 1) t := by
    simpa using (hasDerivAt_id t).const_mul ((j : ℝ) + 1)
  have hcd : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hs := (hcd.differentiable (by simp) (((j : ℝ) + 1) * t)).hasDerivAt.comp t hm
  have hmul := (hasDerivAt_id t).mul hs
  have hcoef : 1 * Real.smoothTransition (((j : ℝ) + 1) * t) +
      id t * (deriv Real.smoothTransition (((j : ℝ) + 1) * t) * ((j : ℝ) + 1)) =
      positivePartSlope j t := by
    simp only [id_eq, positivePartSlope]
    ring
  change HasDerivAt (smoothPositivePart j)
    (1 * Real.smoothTransition (((j : ℝ) + 1) * t) +
      id t * (deriv Real.smoothTransition (((j : ℝ) + 1) * t) * ((j : ℝ) + 1))) t at hmul
  rw [hcoef] at hmul
  exact hmul

theorem smoothPositivePart_eq_zero_of_nonpos (j : ℕ) {t : ℝ} (ht : t ≤ 0) :
    smoothPositivePart j t = 0 := by
  have hm : 0 ≤ (j : ℝ) + 1 := by positivity
  simp [smoothPositivePart, Real.smoothTransition.zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hm ht)]

theorem positivePartSlope_eq_zero_of_nonpos (j : ℕ) {t : ℝ} (ht : t ≤ 0) :
    positivePartSlope j t = 0 := by
  have hm : 0 ≤ (j : ℝ) + 1 := by positivity
  have hmt := mul_nonpos_of_nonneg_of_nonpos hm ht
  simp [positivePartSlope, Real.smoothTransition.zero_of_nonpos hmt,
    deriv_smoothTransition_of_nonpos hmt]

theorem smoothPositivePart_eq_self_of_one_le (j : ℕ) {t : ℝ}
    (ht : 1 ≤ ((j : ℝ) + 1) * t) : smoothPositivePart j t = t := by
  simp [smoothPositivePart, Real.smoothTransition.one_of_one_le ht]

theorem positivePartSlope_eq_one_of_one_le (j : ℕ) {t : ℝ}
    (ht : 1 ≤ ((j : ℝ) + 1) * t) : positivePartSlope j t = 1 := by
  simp [positivePartSlope, Real.smoothTransition.one_of_one_le ht,
    deriv_smoothTransition_of_one_le ht]

theorem smoothPositivePart_norm_le (j : ℕ) (t : ℝ) :
    ‖smoothPositivePart j t‖ ≤ ‖t‖ := by
  rw [smoothPositivePart, norm_mul]
  have hs : ‖Real.smoothTransition (((j : ℝ) + 1) * t)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  exact (mul_le_mul_of_nonneg_left hs (norm_nonneg t)).trans_eq (mul_one _)

theorem positivePartSlope_uniform_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (j : ℕ) (t : ℝ), ‖positivePartSlope j t‖ ≤ C := by
  let d : ℝ → ℝ := fun s => Real.smoothTransition s + s * deriv Real.smoothTransition s
  have hcd : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hc : Continuous d := Real.smoothTransition.continuous.add
    (continuous_id.mul (hcd.continuous_deriv (by simp)))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hc.continuousOn
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro j t
  let s : ℝ := ((j : ℝ) + 1) * t
  change ‖d s‖ ≤ max 1 C
  by_cases hs0 : s ≤ 0
  · simp only [d, Real.smoothTransition.zero_of_nonpos hs0,
      deriv_smoothTransition_of_nonpos hs0, mul_zero, add_zero, norm_zero]
    exact (zero_le_one.trans (le_max_left _ _))
  · by_cases hs1 : 1 ≤ s
    · simp only [d, Real.smoothTransition.one_of_one_le hs1,
        deriv_smoothTransition_of_one_le hs1, mul_zero, add_zero, norm_one]
      exact le_max_left _ _
    · exact (hC s ⟨(lt_of_not_ge hs0).le, (lt_of_not_ge hs1).le⟩).trans (le_max_right _ _)

theorem smoothPositivePart_eventually_eq (t : ℝ) :
    ∀ᶠ j : ℕ in atTop, smoothPositivePart j t = max t 0 := by
  by_cases ht : t ≤ 0
  · exact Eventually.of_forall (fun j => by
      rw [smoothPositivePart_eq_zero_of_nonpos j ht, max_eq_right ht])
  · have hp : 0 < t := lt_of_not_ge ht
    have hlim : Tendsto (fun j : ℕ => ((j : ℝ) + 1) * t) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const hp
    filter_upwards [hlim.eventually (eventually_ge_atTop 1)] with j hj
    rw [smoothPositivePart_eq_self_of_one_le j hj, max_eq_left hp.le]

theorem positivePartSlope_eventually_eq (t : ℝ) :
    ∀ᶠ j : ℕ in atTop, positivePartSlope j t = if 0 < t then 1 else 0 := by
  by_cases ht : t ≤ 0
  · exact Eventually.of_forall (fun j => by
      rw [positivePartSlope_eq_zero_of_nonpos j ht, if_neg (not_lt.mpr ht)])
  · have hp : 0 < t := lt_of_not_ge ht
    have hlim : Tendsto (fun j : ℕ => ((j : ℝ) + 1) * t) atTop atTop :=
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const hp
    filter_upwards [hlim.eventually (eventually_ge_atTop 1)] with j hj
    rw [positivePartSlope_eq_one_of_one_le j hj, if_pos hp]

theorem gradient_smoothPositivePart_comp {n : ℕ} {u : Space n → ℝ}
    (hu : Differentiable ℝ u) (j : ℕ) (x : Space n) :
    gradient (fun y => smoothPositivePart j (u y)) x =
      positivePartSlope j (u x) • gradient u x := by
  have hder := (smoothPositivePart_hasDerivAt j (u x)).comp_hasFDerivAt x (hu x).hasFDerivAt
  unfold gradient
  change (InnerProductSpace.toDual ℝ (Space n)).symm (fderiv ℝ (smoothPositivePart j ∘ u) x) = _
  rw [hder.fderiv]
  exact map_smul (InnerProductSpace.toDual ℝ (Space n)).symm _ _

end BMCompactPDE
#print axioms BMCompactPDE.smoothPositivePart_hasDerivAt
#print axioms BMCompactPDE.positivePartSlope_uniform_bound
#print axioms BMCompactPDE.smoothPositivePart_eventually_eq
#print axioms BMCompactPDE.positivePartSlope_eventually_eq
#print axioms BMCompactPDE.gradient_smoothPositivePart_comp
