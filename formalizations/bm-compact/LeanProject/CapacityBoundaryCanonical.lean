import CapacityBoundaryAEUniqueness

/-! A wire-safe actual capacitary pair, constructed and unique up to global
almost-everywhere equality of both scalar and gradient. Only already published
raw scalar/Sobolev/capacity definitions occur in this statement. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem exists_variational_capacity_potential_unique_up_to_ae
    {n : ℕ} {p : ℝ} (hp : 1<p) (hpn : p<(n : ℝ))
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      MemLp u (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume ∧
      MemLp g (ENNReal.ofReal p) volume ∧
      (∀ D : Set (Space n), Bornology.IsBounded D → SobolevPair p D u g) ∧
      WeakPHarmonicPair p Kᶜ u g ∧
      BMCompactCapacityV2.relativeCapacity p K univ=ENNReal.ofReal (∫ x,‖g x‖^p ∂volume) ∧
      (∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K univ (φ j)) ∧
        Tendsto (fun j => eLpNorm (φ j-u) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume) atTop (𝓝 0) ∧
        Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0)) ∧
      ∀ (v : Space n → ℝ) (h : Space n → Space n),
        MemLp v (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume →
        MemLp h (ENNReal.ofReal p) volume →
        BMCompactCapacityV2.relativeCapacity p K univ=ENNReal.ofReal (∫ x,‖h x‖^p ∂volume) →
        (∃ ψ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K univ (ψ j)) ∧
          Tendsto (fun j => eLpNorm (ψ j-v) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume) atTop (𝓝 0) ∧
          Tendsto (fun j => eLpNorm (fun x => gradient (ψ j) x-h x) (ENNReal.ofReal p) volume) atTop (𝓝 0)) →
        u =ᵐ[volume] v ∧ g =ᵐ[volume] h := by
  obtain ⟨u,g,hu,hg,hSob,hH,hcap,hApprox⟩ := exists_variational_capacity_potential hp hpn hK
  refine ⟨u,g,hu,hg,hSob,hH,hcap,hApprox,?_⟩
  intro v h hv hh hcv hav
  exact variational_capacity_potentials_ae_unique hp hpn hK hu hg hv hh hcap hcv hApprox hav

end BMCompactPDE
#print axioms BMCompactPDE.exists_variational_capacity_potential_unique_up_to_ae
