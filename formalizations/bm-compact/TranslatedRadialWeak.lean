import RadialWeakHarmonic

/-! Translation of the actual smooth radial fundamental profile. This is
proved with its actual classical gradient, local Sobolev membership and
trace divergence, rather than postulating translation invariance of the weak
PDE. No claim about the remainder at infinity is included in this file. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

theorem hasGradientAt_fundamentalPotential_sub
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (n : ℕ) {σ p : ℝ}
    (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (a : E)
    {x : E} (hx : x ≠ a) :
    HasGradientAt (fun y : E => fundamentalPotential n σ p (y - a))
      (normalizedRadialGradient n σ p (x - a)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert!
    (hasGradientAt_fundamentalPotential n hn hpn (sub_ne_zero.mpr hx)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const a) using 1 <;> simp

theorem pFlux_gradient_fundamentalPotential_sub (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (a : Space n)
    {x : Space n} (hx : x ≠ a) :
    pFlux p (gradient (fun y : Space n => fundamentalPotential n σ p (y - a)) x) =
      radialSourceFlux n σ (x - a) := by
  rw [(hasGradientAt_fundamentalPotential_sub n hn hpn a hx).gradient]
  exact pFlux_normalizedRadialGradient n hσ (lt_of_lt_of_le hn hpn) (sub_ne_zero.mpr hx)

theorem contDiffOn_fundamentalPotential_sub (n : ℕ) (σ p : ℝ) (a : Space n) :
    ContDiffOn ℝ ∞ (fun x : Space n => fundamentalPotential n σ p (x - a))
      {x : Space n | x ≠ a} := by
  intro x hx
  exact ((contDiffAt_fundamentalPotential n σ p (sub_ne_zero.mpr hx)).comp x
    (contDiffAt_id.sub contDiffAt_const)).contDiffWithinAt

theorem contDiffOn_pFlux_gradient_fundamentalPotential_sub (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (a : Space n) :
    ContDiffOn ℝ ∞
      (fun x : Space n => pFlux p
        (gradient (fun y : Space n => fundamentalPotential n σ p (y - a)) x))
      {x : Space n | x ≠ a} := by
  have hc : ContDiffOn ℝ ∞ (fun x : Space n => radialSourceFlux n σ (x - a))
      {x : Space n | x ≠ a} := by
    intro x hx
    exact ((contDiffAt_radialSourceFlux n σ (sub_ne_zero.mpr hx)).comp x
      (contDiffAt_id.sub contDiffAt_const)).contDiffWithinAt
  apply hc.congr
  intro x hx
  exact pFlux_gradient_fundamentalPotential_sub n hσ hn hpn a hx

theorem classicalDivergence_comp_sub_const
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : E → E} (a x : E) (hF : DifferentiableAt ℝ F (x - a)) :
    classicalDivergence (fun y : E => F (y - a)) x =
      classicalDivergence F (x - a) := by
  have hc : HasFDerivAt (fun y : E => F (y - a)) (fderiv ℝ F (x - a)) x := by
    convert! hF.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a) using 1 <;> simp
  unfold classicalDivergence
  rw [hc.fderiv]

theorem classicalDivergence_pFlux_gradient_fundamentalPotential_sub (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (a : Space n)
    {x : Space n} (hx : x ≠ a) :
    classicalDivergence
      (fun y : Space n => pFlux p
        (gradient (fun z : Space n => fundamentalPotential n σ p (z - a)) y)) x = 0 := by
  have heq : (fun y : Space n => pFlux p
      (gradient (fun z : Space n => fundamentalPotential n σ p (z - a)) y))
      =ᶠ[𝓝 x] (fun y : Space n => radialSourceFlux n σ (y - a)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact pFlux_gradient_fundamentalPotential_sub n hσ hn hpn a hy
  calc
    classicalDivergence
        (fun y : Space n => pFlux p
          (gradient (fun z : Space n => fundamentalPotential n σ p (z - a)) y)) x =
        classicalDivergence (fun y : Space n => radialSourceFlux n σ (y - a)) x := by
      unfold classicalDivergence
      rw [heq.fderiv_eq]
    _ = classicalDivergence (radialSourceFlux n σ) (x - a) :=
      classicalDivergence_comp_sub_const a x
        ((contDiffAt_radialSourceFlux n σ (sub_ne_zero.mpr hx)).differentiableAt (by simp))
    _ = 0 := classicalDivergence_radialSourceFlux n σ (by simp [Space]) (sub_ne_zero.mpr hx)

/-- The actual translated radial profile has a genuine weak gradient and
satisfies every zero-boundary Sobolev test equation off its translated pole. -/
theorem weakPHarmonicPair_fundamentalPotential_sub (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (a : Space n) :
    WeakPHarmonicPair p {x : Space n | x ≠ a}
      (fun x : Space n => fundamentalPotential n σ p (x - a))
      (gradient (fun x : Space n => fundamentalPotential n σ p (x - a))) := by
  have hp : 1 < p := lt_of_lt_of_le hn hpn
  apply weakPHarmonicPair_of_classicalDivergence_eq_zero hp isOpen_ne
    (locallySobolevPair_of_contDiffOn hp isOpen_ne (contDiffOn_fundamentalPotential_sub n σ p a))
    (contDiffOn_pFlux_gradient_fundamentalPotential_sub n hσ hn hpn a)
  intro x hx
  exact classicalDivergence_pFlux_gradient_fundamentalPotential_sub n hσ hn hpn a hx

theorem isWeakPHarmonic_fundamentalPotential_sub (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p) (a : Space n) :
    IsWeakPHarmonic p {x : Space n | x ≠ a}
      (fun x : Space n => fundamentalPotential n σ p (x - a)) :=
  ⟨gradient (fun x : Space n => fundamentalPotential n σ p (x - a)),
    weakPHarmonicPair_fundamentalPotential_sub n hσ hn hpn a⟩

end BMCompactPDE
#print axioms BMCompactPDE.hasGradientAt_fundamentalPotential_sub
#print axioms BMCompactPDE.pFlux_gradient_fundamentalPotential_sub
#print axioms BMCompactPDE.contDiffOn_fundamentalPotential_sub
#print axioms BMCompactPDE.contDiffOn_pFlux_gradient_fundamentalPotential_sub
#print axioms BMCompactPDE.classicalDivergence_comp_sub_const
#print axioms BMCompactPDE.classicalDivergence_pFlux_gradient_fundamentalPotential_sub
#print axioms BMCompactPDE.weakPHarmonicPair_fundamentalPotential_sub
#print axioms BMCompactPDE.isWeakPHarmonic_fundamentalPotential_sub
