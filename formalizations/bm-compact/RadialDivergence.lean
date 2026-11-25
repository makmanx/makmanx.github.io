import FundamentalProfiles
import RadialDivergenceCore

noncomputable section
set_option autoImplicit false
open InnerProductSpace Filter Topology
open scoped InnerProductSpace
namespace BMCompactPDE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]


/-- The source's explicit fundamental profile solves the classical p-Laplace
equation off the origin. This is not the distributional point-source identity. -/
theorem classicalDivergence_pFlux_gradient_fundamentalPotential (n : ℕ) {σ p : ℝ}
    (hσ : 0 < σ) (hn : 1 < (n : ℝ)) (hpn : (n : ℝ) ≤ p)
    (hdim : Module.finrank ℝ E = n) {x : E} (hx : x ≠ 0) :
    classicalDivergence
      (fun y => pFlux p (gradient (fundamentalPotential n σ p : E → ℝ) y)) x = 0 := by
  have heq : (fun y => pFlux p (gradient (fundamentalPotential n σ p : E → ℝ) y))
      =ᶠ[𝓝 x] radialSourceFlux n σ := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact pFlux_gradient_fundamentalPotential n hσ hn hpn hy
  unfold classicalDivergence
  rw [heq.fderiv_eq]
  exact classicalDivergence_radialSourceFlux n σ hdim hx

end BMCompactPDE

#print axioms BMCompactPDE.classicalDivergence_pFlux_gradient_fundamentalPotential
