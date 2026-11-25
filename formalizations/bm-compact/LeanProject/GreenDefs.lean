import WeakPDE
import FundamentalProfiles
import Mathlib.Topology.MetricSpace.Bounded

/-!
Concrete Green-function data corresponding to manuscript eqn2.9.  The
normalization parameter σ remains explicit; no identification with Hausdorff
sphere area or general existence/uniqueness theorem is built into these data.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology

namespace BMCompactPDE

/-- Bounded perturbation of the actual radial fundamental profile near infinity. -/
def HasBoundedGreenRemainder (n : ℕ) (σ p : ℝ)
    (G : Space n → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in cobounded (Space n),
    |G x - fundamentalPotential n σ p x| ≤ C

/-- Concrete exterior Green predicate; all PDE content is the actual weak
p-Laplace equation, never a postulated abstract Green operator. -/
def IsExteriorGreen (n : ℕ) (σ p : ℝ) (K : Set (Space n))
    (G : Space n → ℝ) : Prop :=
  1 < (n : ℝ) ∧ (n : ℝ) ≤ p ∧ 0 < σ ∧
    IsCompact K ∧ K.Nonempty ∧ Continuous G ∧
    EqOn G (fun _ => 0) K ∧ IsWeakPHarmonic p Kᶜ G ∧
    HasBoundedGreenRemainder n σ p G

/-- A finite actual asymptotic constant, a separate requirement until its
existence is proved for a given Green function. -/
def HasGreenAsymptotic (n : ℕ) (σ p : ℝ) (G : Space n → ℝ) (k : ℝ) : Prop :=
  Tendsto (fun x => G x - fundamentalPotential n σ p x)
    (cobounded (Space n)) (nhds k)

/-- The radial formula evaluated at a positive real radius. -/
def fundamentalRadialValue (n : ℕ) (σ p r : ℝ) : ℝ :=
  fundamentalPotential n σ p (r : ℝ)

/-- Explicit ball candidate: flatten the profile on the closed radius-R ball.
For R>0 this avoids the critical profile's singularity at the origin. -/
def ballGreen (n : ℕ) (σ p R : ℝ) (x : Space n) : ℝ :=
  fundamentalRadialValue n σ p (max R ‖x‖) - fundamentalRadialValue n σ p R

/-- Scalar recipe in eqn2.10. This definition alone does not assign capacity
to an arbitrary compact set or assert the existence of an asymptotic constant. -/
def greenCapacityOfConstant (n : ℕ) (σ p k : ℝ) : ℝ :=
  if p = (n : ℝ) then Real.exp (-k / σ ^ (-((n : ℝ) - 1)⁻¹))
  else (-k) ^ (p - 1)

end BMCompactPDE
