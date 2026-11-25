import ExteriorContinuousPotential
import WeakHarmonicScaling

/-! Pointwise interior unit bounds for the selected variational potential.
Only its already constructed exterior continuous representative is used;
no continuity across K or pointwise trace on K is asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem boundary_pointwise_bounds_of_ae {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hb : ∀ᵐ x ∂volume.restrict Ω, 0≤u x ∧ u x≤1) :
    ∀ x∈Ω, 0≤u x ∧ u x≤1 := by
  have hlow : (fun x => max (-u x) 0) =ᵐ[volume.restrict Ω] (fun _ => 0) := by
    filter_upwards [hb] with x hx
    exact max_eq_right (neg_nonpos.mpr hx.1)
  have hupp : (fun x => max (u x-1) 0) =ᵐ[volume.restrict Ω] (fun _ => 0) := by
    filter_upwards [hb] with x hx
    exact max_eq_right (sub_nonpos.mpr hx.2)
  have hl := Measure.eqOn_open_of_ae_eq hlow hΩ
    ((show Continuous (fun r : ℝ => max (-r) 0) by fun_prop).comp_continuousOn hu) continuousOn_const
  have hh := Measure.eqOn_open_of_ae_eq hupp hΩ
    ((show Continuous (fun r : ℝ => max (r-1) 0) by fun_prop).comp_continuousOn hu) continuousOn_const
  intro x hx
  have hlo : -u x≤0 := (le_max_left (-u x) 0).trans_eq (hl hx)
  have hup : u x-1≤0 := (le_max_left (u x-1) 0).trans_eq (hh hx)
  exact ⟨neg_nonpos.mp hlo, sub_nonpos.mp hup⟩

theorem exists_continuous_exterior_capacity_potential_pointwise_bounds {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) {K : Set (Space n)} (hK : IsCompact K) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      MemLp u (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume ∧
      MemLp g (ENNReal.ofReal p) volume ∧
      (∀ D : Set (Space n), Bornology.IsBounded D → SobolevPair p D u g) ∧
      ContinuousOn u Kᶜ ∧ WeakPHarmonicPair p Kᶜ u g ∧
      (∀ x∈Kᶜ, 0≤u x ∧ u x≤1) ∧
      (∀ᵐ x ∂volume, 0≤u x ∧ u x≤1) ∧
      BMCompactCapacityV2.relativeCapacity p K univ = ENNReal.ofReal (∫ x, ‖g x‖^p ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ, (∀ j, BMCompactCapacityV2.Admissible K univ (φ j)) ∧
        Tendsto (fun j => eLpNorm (φ j-u) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume) atTop (𝓝 0) ∧
        Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  obtain ⟨u,g,hu,hg,hSob,hcont,hH,hunit,hcap,happrox⟩ :=
    exists_continuous_exterior_variational_capacity_potential hp hpn hK
  exact ⟨u,g,hu,hg,hSob,hcont,hH,
    boundary_pointwise_bounds_of_ae hK.isClosed.isOpen_compl hcont (ae_restrict_of_ae hunit),
    hunit,hcap,happrox⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_continuous_exterior_capacity_potential_pointwise_bounds
