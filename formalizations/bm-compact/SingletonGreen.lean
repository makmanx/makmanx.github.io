import GreenDefs
import RadialWeakHarmonic
import RadialGlobalContinuity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Actual supercritical singleton exterior Green witness. The parameter σ
is explicit. No general compact-set existence or uniqueness is asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology
namespace BMCompactPDE

/-- The actual profile with zero asymptotic remainder is a Green witness for
one point in the supercritical regime. -/
theorem isExteriorGreen_singleton_fundamentalPotential (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) < p) :
    IsExteriorGreen n σ p ({0} : Set (Space n)) (fundamentalPotential n σ p) := by
  refine ⟨hn, hpn.le, hσ, isCompact_singleton, singleton_nonempty 0,
    continuous_fundamentalPotential_supercritical n σ hn hpn, ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_singleton_iff.mp hx with rfl
    exact fundamentalPotential_zero_of_supercritical n σ hn hpn
  · exact isWeakPHarmonic_fundamentalPotential n hσ hn hpn.le
  · refine ⟨0, le_rfl, Eventually.of_forall ?_⟩
    intro x
    simp

theorem hasGreenAsymptotic_fundamentalPotential (n : ℕ) (σ p : ℝ) :
    HasGreenAsymptotic n σ p (fundamentalPotential n σ p) 0 := by
  simpa only [HasGreenAsymptotic, sub_self] using
    (tendsto_const_nhds : Tendsto (fun _ : Space n => (0 : ℝ))
      (cobounded (Space n)) (𝓝 0))

/-- The scalar source capacity recipe is zero for this actual supercritical
singleton Green witness. Choice independence is a separate uniqueness theorem. -/
theorem greenCapacityOfConstant_zero_supercritical (n : ℕ) {σ p : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) < p) :
    greenCapacityOfConstant n σ p 0 = 0 := by
  simp only [greenCapacityOfConstant, if_neg (ne_of_gt hpn), neg_zero,
    Real.zero_rpow (ne_of_gt (sub_pos.mpr (hn.trans hpn)))]

end BMCompactPDE
#print axioms BMCompactPDE.isExteriorGreen_singleton_fundamentalPotential
#print axioms BMCompactPDE.hasGreenAsymptotic_fundamentalPotential
#print axioms BMCompactPDE.greenCapacityOfConstant_zero_supercritical
