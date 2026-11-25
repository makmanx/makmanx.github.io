import RadialSobolev
import RadialFluxSmooth
import WeakClassicalDivergence

/-! The source's explicit radial profile is weak p-harmonic away from the
origin in the full W^{1,p}_0 test class. Local Sobolev membership is proved,
not retained as an extra hypothesis. The positive normalization parameter
remains explicit; the distributional delta-source identity is separate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

theorem weakPHarmonicPair_fundamentalPotential (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) :
    WeakPHarmonicPair p {x : Space n | x ≠ 0}
      (fundamentalPotential n σ p) (gradient (fundamentalPotential n σ p)) := by
  have hp : 1 < p := lt_of_lt_of_le hn hpn
  apply weakPHarmonicPair_of_classicalDivergence_eq_zero hp
    isOpen_ne
    (locallySobolevPair_fundamentalPotential n σ p hp)
    (contDiffOn_pFlux_gradient_fundamentalPotential n hσ hn hpn)
  intro x hx
  exact classicalDivergence_pFlux_gradient_fundamentalPotential n hσ hn hpn
    (by simp [Space]) hx

theorem isWeakPHarmonic_fundamentalPotential (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) :
    IsWeakPHarmonic p {x : Space n | x ≠ 0} (fundamentalPotential n σ p) :=
  ⟨gradient (fundamentalPotential n σ p),
    weakPHarmonicPair_fundamentalPotential n hσ hn hpn⟩

end BMCompactPDE
#print axioms BMCompactPDE.weakPHarmonicPair_fundamentalPotential
#print axioms BMCompactPDE.isWeakPHarmonic_fundamentalPotential
