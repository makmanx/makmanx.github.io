import UpstreamGreenActualGradientLimit
import UpstreamGreenAnnularLimitBoundary
import UpstreamGreenAnnularLimitRemainder

/-! Genuine canonical weak exterior Green existence above the dimension.
The SAME constructed annular scalar/gradient limit supplies the actual weak
PDE, global zero-trace continuity and bounded fundamental-profile remainder.
No potential, convergence, regularity, boundary trace or asymptotic bound is
an input. A finite asymptotic constant and nonlinear C1 are not asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem exists_canonical_exterior_green_supercritical
    {n : ℕ} {p : ℝ} (hn : 2≤n) (hnp : (n:ℝ)<p)
    {K : Set (Space n)} (hK : IsCompact K) (h0 : (0 : Space n)∈K) :
    ∃ v : Space n → ℝ,∃ g : Space n → Space n,
      IsExteriorGreen n (canonicalSphereArea n) p K v ∧ WeakPHarmonicPair p Kᶜ v g ∧
      (∀ a∈K,∀ x,0≤v x ∧ v x≤fundamentalPotential n (canonicalSphereArea n) p (x-a)) ∧
      ∃ a : ℝ,0<a ∧ K⊆closedBall (0 : Space n) a ∧ ∀ x,
        fundamentalPotential n (canonicalSphereArea n) p x-
          fundamentalRadialValue n (canonicalSphereArea n) p a≤v x ∧
        v x≤fundamentalPotential n (canonicalSphereArea n) p x := by
  obtain ⟨R,G,Γ,v,g,-,-,hRlim,hGc,hGK,hGout,-,-,hH,hB,-,hvc,hpoint,-,-,-,hweak,-⟩ :=
    exists_canonical_annular_green_weak_limit_supercritical hn hnp hK h0
  obtain ⟨hcont,hzero,hshift⟩ := continuous_annular_pointwise_limit_with_zero_obstacle
    hn hnp hK hRlim hGc hGK hGout hH (fun j x=>(hB j x).1) hpoint hvc
  obtain ⟨hrem,hlower⟩ := annular_pointwise_limit_has_bounded_canonical_green_remainder
    hn hnp hK hRlim hGc hGout hH hB hpoint
  have hn0 : 0<n := lt_of_lt_of_le (by decide : 0<2) hn
  have hnr : 1<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2) hn)
  have hgreen : IsExteriorGreen n (canonicalSphereArea n) p K v :=
    ⟨hnr,hnp.le,canonicalSphereArea_pos hn0,hK,⟨0,h0⟩,hcont,hzero,⟨g,hweak⟩,hrem⟩
  exact ⟨v,g,hgreen,hweak,hshift,hlower⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_canonical_exterior_green_supercritical
