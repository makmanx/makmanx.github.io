import BMCompactNonlinearChecked
import Mathlib.Tactic.Module

/-! Actual gradient-difference energy foundations.  The weak inputs are the
concrete distributional pairs; no classical derivative of either solution,
selected representative, gradient bound or desired energy estimate is assumed.
These are estimates toward regularity, not a C1 representative theorem. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

section Flux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_power_midpoint_flux_bound {p : ℝ} (hp : 1<p) (v w : E) :
    ‖v‖^p+‖w‖^p-2*‖(1/2 : ℝ) • (v+w)‖^p ≤
      (p/2)*inner ℝ (pFlux p v-pFlux p w) (v-w) := by
  have hv := norm_rpow_add_tangent_lower hp v ((1/2 : ℝ) • (w-v))
  have hw := norm_rpow_add_tangent_lower hp w ((1/2 : ℝ) • (v-w))
  have hmv : v+(1/2 : ℝ) • (w-v)=(1/2 : ℝ) • (v+w) := by module
  have hmw : w+(1/2 : ℝ) • (v-w)=(1/2 : ℝ) • (v+w) := by module
  rw [hmv,inner_smul_right,inner_sub_right] at hv
  rw [hmw,inner_smul_right,inner_sub_right] at hw
  rw [inner_sub_left,inner_sub_right,inner_sub_right]
  nlinarith only [hv,hw]

theorem pFlux_pairing_controls_half_difference {p : ℝ} (hp : 2≤p) (v w : E) :
    4*‖(1/2 : ℝ) • (v-w)‖^p ≤
      p*inner ℝ (pFlux p v-pFlux p w) (v-w) := by
  have hp1 : 1<p := lt_of_lt_of_le (by norm_num : (1 : ℝ)<2) hp
  have hc := BMCompactNonlinear.hilbert_midpoint_clarkson hp v w
  have hf := norm_power_midpoint_flux_bound hp1 v w
  nlinarith only [hc,hf]

end Flux

private theorem sobolev_sub_pair {n : ℕ} {p : ℝ} {D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : SobolevPair p D u g) (hv : SobolevPair p D v h) :
    SobolevPair p D (u-v) (g-h) := by
  simpa only [neg_one_smul,sub_eq_add_neg] using hu.add (hv.smul (-1))

/-- Subtracting two actual linear Poisson equations with the same source
constructs an actual homogeneous weak equation, without boundary conditions. -/
theorem WeakPSourcePair.harmonic_difference_two
    {n : ℕ} {c : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (hv : WeakPSourcePair 2 c Ω v h) :
    WeakPHarmonicPair 2 Ω (u-v) (g-h) := by
  refine ⟨by norm_num,hu.2.1,?_,?_⟩
  · intro D hD
    exact sobolev_sub_pair (hu.2.2.1 D hD) (hv.2.2.1 D hD)
  · intro D hD θ k hθ
    obtain ⟨hi,he⟩ := hu.2.2.2 D hD θ k hθ
    obtain ⟨hj,hf⟩ := hv.2.2.2 D hD θ k hθ
    have hflux : fluxPairing 2 (g-h) k=fluxPairing 2 g k-fluxPairing 2 h k := by
      funext x
      simp only [fluxPairing,pFlux_two,Pi.sub_apply,inner_sub_left]
    refine ⟨?_,?_⟩
    · rw [hflux]
      exact hi.sub hj
    · rw [hflux]
      change (∫ x in D,fluxPairing 2 g k x-fluxPairing 2 h k x)=0
      rw [integral_sub hi hj,he,hf,sub_self]

/-- A genuine local quadratic estimate for the difference of two raw weak
solutions.  In particular it is available for spatial translates once their
actual translated weak equations are established. -/
theorem WeakPSourcePair.gradient_difference_caccioppoli_two
    {n : ℕ} {c : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (hv : WeakPSourcePair 2 c Ω v h)
    (hD : LocalDomain D Ω) {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x,0≤η x) (hη1 : ∀ x,η x≤1) :
    (∫ x in D,η x^2*‖g x-h x‖^2) ≤
      4*∫ x in D,|u x-v x|^2*‖gradient η x‖^2 := by
  have he := (hu.harmonic_difference_two hv).caccioppoli_natPow
    (M := 2) hD hη hη0 hη1 (by norm_num) 0
  norm_num only [Pi.sub_apply,sub_zero,Real.rpow_two,Nat.cast_ofNat] at he
  exact he

end BMCompactPDE
#print axioms BMCompactPDE.norm_power_midpoint_flux_bound
#print axioms BMCompactPDE.pFlux_pairing_controls_half_difference
#print axioms BMCompactPDE.WeakPSourcePair.harmonic_difference_two
#print axioms BMCompactPDE.WeakPSourcePair.gradient_difference_caccioppoli_two
