import BoundaryInfinity

/-! A genuine exterior variational capacity potential with a selected continuous
representative, pointwise unit bounds outside K and the actual zero limit at
infinity, while retaining every global variational/Sobolev/approximation datum.
Boundary traces, continuity across K, C1 and pole/flux normalization remain separate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem exists_continuous_exterior_capacity_potential_vanishing_at_infinity
    {n : ℕ} {p : ℝ} (hp : 1<p) (hpn : p<(n : ℝ))
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      MemLp u (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume ∧
      MemLp g (ENNReal.ofReal p) volume ∧
      (∀ D : Set (Space n), Bornology.IsBounded D → SobolevPair p D u g) ∧
      ContinuousOn u Kᶜ ∧ WeakPHarmonicPair p Kᶜ u g ∧
      (∀ x∈Kᶜ, 0≤u x ∧ u x≤1) ∧
      Tendsto u (cocompact (Space n)) (𝓝 0) ∧
      (∀ᵐ x ∂volume, 0≤u x ∧ u x≤1) ∧
      BMCompactCapacityV2.relativeCapacity p K univ = ENNReal.ofReal (∫ x, ‖g x‖^p ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ, (∀ j, BMCompactCapacityV2.Admissible K univ (φ j)) ∧
        Tendsto (fun j => eLpNorm (φ j-u) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume) atTop (𝓝 0) ∧
        Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  obtain ⟨u,g,hu,hg,hSob,hcont,hH,hpoint,hunit,hcap,φ,hφ,hlu,hlg⟩ :=
    exists_continuous_exterior_capacity_potential_pointwise_bounds hp hpn hK
  have hpq : p≤(n : ℝ)*p/((n : ℝ)-p) := by
    apply (le_div_iff₀ (sub_pos.mpr hpn)).mpr
    nlinarith [sq_nonneg p]
  have hinfty := WeakPHarmonicPair.tendsto_zero_at_infinity_of_compact_lp_approximation
    hK hpn hpq hH hcont hu (fun x hx => (hpoint x hx).1)
    (fun j => (hφ j).1.continuous) (fun j => (hφ j).2.1) hlu
  exact ⟨u,g,hu,hg,hSob,hcont,hH,hpoint,hinfty,hunit,hcap,φ,hφ,hlu,hlg⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_continuous_exterior_capacity_potential_vanishing_at_infinity
