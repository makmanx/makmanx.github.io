import SuperContinuousBatch

/-! Actual translated fundamental primitives for every p>1. The weak equation
is derived from the actual gradient and radial divergence; no translation rule
for nonsmooth weak functions is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

theorem hasGradientAt_fundamentalPotential_sub_all_p
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (n : ℕ) {σ p : ℝ} (hp : 1 < p) (a : E)
    {x : E} (hx : x ≠ a) :
    HasGradientAt (fun y : E => fundamentalPotential n σ p (y-a))
      (normalizedRadialGradient n σ p (x-a)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert!
    (hasGradientAt_fundamentalPotential_all_p n σ hp (sub_ne_zero.mpr hx)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const a) using 1 <;> simp

theorem pFlux_gradient_fundamentalPotential_sub_all_p (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hp : 1 < p) (a : Space n) {x : Space n} (hx : x ≠ a) :
    pFlux p (gradient (fun y : Space n => fundamentalPotential n σ p (y-a)) x) =
      radialSourceFlux n σ (x-a) := by
  rw [(hasGradientAt_fundamentalPotential_sub_all_p n hp a hx).gradient]
  exact pFlux_normalizedRadialGradient n hσ hp (sub_ne_zero.mpr hx)

theorem contDiffOn_pFlux_gradient_fundamentalPotential_sub_all_p
    (n : ℕ) {σ p : ℝ} (hσ : 0 < σ) (hp : 1 < p) (a : Space n) :
    ContDiffOn ℝ ∞ (fun x : Space n => pFlux p
      (gradient (fun y : Space n => fundamentalPotential n σ p (y-a)) x))
      {x : Space n | x ≠ a} := by
  have hc : ContDiffOn ℝ ∞ (fun x : Space n => radialSourceFlux n σ (x-a))
      {x : Space n | x ≠ a} := by
    intro x hx
    exact ((contDiffAt_radialSourceFlux n σ (sub_ne_zero.mpr hx)).comp x
      (contDiffAt_id.sub contDiffAt_const)).contDiffWithinAt
  apply hc.congr
  intro x hx
  exact pFlux_gradient_fundamentalPotential_sub_all_p n hσ hp a hx

theorem classicalDivergence_pFlux_gradient_fundamentalPotential_sub_all_p
    (n : ℕ) {σ p : ℝ} (hσ : 0 < σ) (hp : 1 < p) (a : Space n)
    {x : Space n} (hx : x ≠ a) :
    classicalDivergence (fun y : Space n => pFlux p
      (gradient (fun z : Space n => fundamentalPotential n σ p (z-a)) y)) x = 0 := by
  have heq : (fun y : Space n => pFlux p
      (gradient (fun z : Space n => fundamentalPotential n σ p (z-a)) y))
      =ᶠ[𝓝 x] (fun y : Space n => radialSourceFlux n σ (y-a)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact pFlux_gradient_fundamentalPotential_sub_all_p n hσ hp a hy
  calc
    classicalDivergence (fun y : Space n => pFlux p
        (gradient (fun z : Space n => fundamentalPotential n σ p (z-a)) y)) x =
        classicalDivergence (fun y : Space n => radialSourceFlux n σ (y-a)) x := by
      unfold classicalDivergence
      rw [heq.fderiv_eq]
    _ = classicalDivergence (radialSourceFlux n σ) (x-a) :=
      classicalDivergence_comp_sub_const a x
        ((contDiffAt_radialSourceFlux n σ (sub_ne_zero.mpr hx)).differentiableAt (by simp))
    _ = 0 := classicalDivergence_radialSourceFlux n σ (by simp [Space]) (sub_ne_zero.mpr hx)

theorem weakPHarmonicPair_fundamentalPotential_sub_all_p (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hp : 1 < p) (a : Space n) :
    WeakPHarmonicPair p {x : Space n | x ≠ a}
      (fun x : Space n => fundamentalPotential n σ p (x-a))
      (gradient (fun x : Space n => fundamentalPotential n σ p (x-a))) := by
  apply weakPHarmonicPair_of_classicalDivergence_eq_zero hp isOpen_ne
    (locallySobolevPair_of_contDiffOn hp isOpen_ne
      (contDiffOn_fundamentalPotential_sub n σ p a))
    (contDiffOn_pFlux_gradient_fundamentalPotential_sub_all_p n hσ hp a)
  intro x hx
  exact classicalDivergence_pFlux_gradient_fundamentalPotential_sub_all_p n hσ hp a hx

theorem isWeakPHarmonic_fundamentalPotential_sub_all_p (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hp : 1 < p) (a : Space n) :
    IsWeakPHarmonic p {x : Space n | x ≠ a}
      (fun x : Space n => fundamentalPotential n σ p (x-a)) :=
  ⟨gradient (fun x : Space n => fundamentalPotential n σ p (x-a)),
    weakPHarmonicPair_fundamentalPotential_sub_all_p n hσ hp a⟩

end BMCompactPDE
#print axioms BMCompactPDE.hasGradientAt_fundamentalPotential_sub_all_p
#print axioms BMCompactPDE.pFlux_gradient_fundamentalPotential_sub_all_p
#print axioms BMCompactPDE.contDiffOn_pFlux_gradient_fundamentalPotential_sub_all_p
#print axioms BMCompactPDE.classicalDivergence_pFlux_gradient_fundamentalPotential_sub_all_p
#print axioms BMCompactPDE.weakPHarmonicPair_fundamentalPotential_sub_all_p
#print axioms BMCompactPDE.isWeakPHarmonic_fundamentalPotential_sub_all_p
