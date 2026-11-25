import BMCompactChecked
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Actual variational local minimization follows from the full weak equation,
without any classical differentiability of the Sobolev representative. This is
an energy foundation for regularity, not a continuity or C1 estimate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology
namespace BMCompactPDE

section Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine p-energy density lies above its genuine flux tangent plane. -/
theorem norm_rpow_tangent_lower {p : ℝ} (hp : 1 < p) (v w : E) :
    ‖v‖ ^ p + p * inner ℝ (pFlux p v) (w-v) ≤ ‖w‖ ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hm : p-1 ≠ 0 := (sub_pos.mpr hp).ne'
  have hy := Real.young_inequality_of_nonneg (norm_nonneg w) (norm_nonneg (pFlux p v))
    (Real.HolderConjugate.conjExponent hp)
  change ‖w‖ * ‖pFlux p v‖ ≤ ‖w‖ ^ p / p + ‖pFlux p v‖ ^ (p/(p-1)) / (p/(p-1)) at hy
  rw [norm_pFlux_dual_power hp] at hy
  have hmul := mul_le_mul_of_nonneg_left hy hp0.le
  have heq : p * (‖w‖ ^ p / p + ‖v‖ ^ p / (p/(p-1))) =
      ‖w‖ ^ p + (p-1) * ‖v‖ ^ p := by
    field_simp [hp0.ne',hm]
  rw [heq] at hmul
  have hcs := mul_le_mul_of_nonneg_left (real_inner_le_norm (pFlux p v) w) hp0.le
  rw [inner_sub_right,pFlux_inner_self hp]
  nlinarith

theorem norm_rpow_add_tangent_lower {p : ℝ} (hp : 1 < p) (v h : E) :
    ‖v‖ ^ p + p * inner ℝ (pFlux p v) h ≤ ‖v+h‖ ^ p := by
  simpa only [add_sub_cancel_left] using norm_rpow_tangent_lower hp v (v+h)

end Pointwise

/-- Actual Lp membership supplies finite real p-energy; it is not an extra
hypothesis of the minimization theorem. -/
theorem integrable_norm_rpow_of_memLp {n : ℕ} {p : ℝ} (hp : 1 < p)
    {μ : Measure (Space n)} {g : Space n → Space n}
    (hg : MemLp g (ENNReal.ofReal p) μ) : Integrable (fun x => ‖g x‖ ^ p) μ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  simpa only [ENNReal.toReal_ofReal hp0.le] using
    hg.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top

/-- Every actual local weak p-harmonic pair minimizes the actual p-energy
against every concrete zero-boundary Sobolev perturbation. No regularity of u
or conclusion-equivalent minimizer premise is supplied. -/
theorem WeakPHarmonicPair.local_energy_minimizer {n : ℕ} {p : ℝ}
    {Ω D : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hD : LocalDomain D Ω)
    {θ : Space n → ℝ} {h : Space n → Space n}
    (hθ : ZeroBoundarySobolevPair p D θ h) :
    (∫ x in D, ‖g x‖ ^ p) ≤ ∫ x in D, ‖g x+h x‖ ^ p := by
  have hg := (hu.2.2.1 D hD).2.2.1
  have hh := hθ.1.2.2.1
  have hi := integrable_norm_rpow_of_memLp hu.1 hg
  have hj := integrable_norm_rpow_of_memLp hu.1 (hg.add hh)
  obtain ⟨hpair,hzero⟩ := hu.2.2.2 D hD θ h hθ
  have hle := integral_mono (hi.add (hpair.const_mul p)) hj
    (fun x => norm_rpow_add_tangent_lower hu.1 (g x) (h x))
  simp only [Pi.add_apply] at hle
  rw [integral_add hi (hpair.const_mul p),integral_const_mul,hzero,mul_zero,add_zero] at hle
  exact hle

end BMCompactPDE
#print axioms BMCompactPDE.norm_rpow_tangent_lower
#print axioms BMCompactPDE.norm_rpow_add_tangent_lower
#print axioms BMCompactPDE.integrable_norm_rpow_of_memLp
#print axioms BMCompactPDE.WeakPHarmonicPair.local_energy_minimizer
