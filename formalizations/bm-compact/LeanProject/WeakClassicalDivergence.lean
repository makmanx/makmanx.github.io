import WeakDivergence
import EuclideanDivergence

/-! Trace-based classical divergence implies the complete weak p-Laplace
equation.  Local Sobolev membership remains an explicit mathematical input;
it is not inferred merely from a pointwise flux identity. -/

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace BMCompactPDE

theorem weakPHarmonicPair_of_classicalDivergence_eq_zero {n : ℕ} {p : ℝ}
    (hp : 1 < p) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hSob : LocallySobolevPair p Ω u g)
    (hflux : ContDiffOn ℝ ∞ (fun x => pFlux p (g x)) Ω)
    (hdiv : ∀ x ∈ Ω, classicalDivergence (fun y => pFlux p (g y)) x = 0) :
    WeakPHarmonicPair p Ω u g := by
  apply weakPHarmonicPair_of_divergence_eq_zero hp hΩ hSob
  · intro i
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hflux
  · intro x hx
    have hd : DifferentiableAt ℝ (fun y => pFlux p (g y)) x :=
      (hflux.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
    change (∑ i : Fin n, (gradient (fun y => pFlux p (g y) i) x) i) = 0
    rw [← classicalDivergence_eq_sum_gradient_coordinates hd]
    exact hdiv x hx

end BMCompactPDE

#print axioms BMCompactPDE.weakPHarmonicPair_of_classicalDivergence_eq_zero
