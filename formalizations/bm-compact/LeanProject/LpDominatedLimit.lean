import WeakDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A finite-p dominated-convergence lemma stated directly in the eLpNorm
language of the concrete Sobolev graph. -/
noncomputable section
set_option autoImplicit false
open Filter MeasureTheory
open scoped ENNReal Topology
namespace BMCompactPDE

theorem tendsto_eLpNorm_zero_of_dominated
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {q : ℝ≥0∞} (hq0 : q ≠ 0) (hqtop : q ≠ ∞)
    {f : ℕ → α → E} {b : α → E}
    (hf : ∀ j, AEStronglyMeasurable (f j) μ) (hb : MemLp b q μ)
    (hbound : ∀ j, ∀ᵐ x ∂μ, ‖f j x‖ ≤ ‖b x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (f j) q μ) atTop (𝓝 0) := by
  have hqpos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hmeas (j : ℕ) : AEMeasurable (fun x => ‖f j x‖ₑ ^ q.toReal) μ :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hf j).enorm
  have hbd (j : ℕ) : ∀ᵐ x ∂μ, ‖f j x‖ₑ ^ q.toReal ≤ ‖b x‖ₑ ^ q.toReal := by
    filter_upwards [hbound j] with x hx
    apply ENNReal.rpow_le_rpow _ hqpos.le
    change (‖f j x‖₊ : ℝ≥0∞) ≤ (‖b x‖₊ : ℝ≥0∞)
    exact ENNReal.coe_le_coe.mpr (by exact_mod_cast hx)
  have hpt : ∀ᵐ x ∂μ, Tendsto (fun j => ‖f j x‖ₑ ^ q.toReal) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    simpa only [enorm_zero, ENNReal.zero_rpow_of_pos hqpos] using
      hx.enorm.ennrpow_const q.toReal
  have hi := tendsto_lintegral_of_dominated_convergence'
    (fun x => ‖b x‖ₑ ^ q.toReal) hmeas hbd
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hq0 hqtop hb.2).ne hpt
  have h0 : (∫⁻ _x : α, (0 : ℝ≥0∞) ∂μ) = 0 := by simp
  rw [h0] at hi
  have hout := hi.ennrpow_const (1 / q.toReal)
  simpa only [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop,
    ENNReal.zero_rpow_of_pos (one_div_pos.mpr hqpos)] using hout

end BMCompactPDE
#print axioms BMCompactPDE.tendsto_eLpNorm_zero_of_dominated
