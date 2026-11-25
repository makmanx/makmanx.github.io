import ExteriorCapacityClamp
import RootSourceContinuity

/-! A constructed exterior continuous representative retaining the genuine
global variational data. The selected representative is patched only on K^c;
the original scalar stays on K, so global AE equality is proved before any
Lp/Sobolev/density transfer. Continuity across boundary K is NOT asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem exists_continuous_exterior_variational_capacity_potential {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) {K : Set (Space n)} (hK : IsCompact K) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      MemLp u (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume ∧
      MemLp g (ENNReal.ofReal p) volume ∧
      (∀ D : Set (Space n), Bornology.IsBounded D → SobolevPair p D u g) ∧
      ContinuousOn u Kᶜ ∧ WeakPHarmonicPair p Kᶜ u g ∧
      (∀ᵐ x ∂volume, 0≤u x ∧ u x≤1) ∧
      BMCompactCapacityV2.relativeCapacity p K univ = ENNReal.ofReal (∫ x, ‖g x‖^p ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ, (∀ j, BMCompactCapacityV2.Admissible K univ (φ j)) ∧
        Tendsto (fun j => eLpNorm (φ j-u) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume) atTop (𝓝 0) ∧
        Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  classical
  obtain ⟨u, g, hu, hg, hSob, hH, hunit, hcap, φ, hφ, hlu, hlg⟩ :=
    exists_variational_capacity_potential_unit_bounds hp hpn hK
  obtain ⟨v, hv, huv, -⟩ := hH.source_zero.exists_continuous_weak_representative hpn
  let U : Space n → ℝ := K.piecewise u v
  have hlocal : ∀ᵐ x ∂volume, x∉K → u x=v x :=
    (ae_restrict_iff' hK.isClosed.measurableSet.compl).mp huv
  have hglobal : u =ᵐ[volume] U := by
    filter_upwards [hlocal] with x hx
    by_cases hxK : x∈K
    · simp only [U, Set.piecewise, if_pos hxK]
    · simpa only [U, Set.piecewise, if_neg hxK] using hx hxK
  have hUv : EqOn U v Kᶜ := by
    intro x hx
    have hxK : x∉K := hx
    simp only [U, Set.piecewise, if_neg hxK]
  have hUcont : ContinuousOn U Kᶜ := hv.congr hUv
  have hUmem : MemLp U (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume :=
    (memLp_congr_ae hglobal).mp hu
  have hUSob : ∀ D : Set (Space n), Bornology.IsBounded D → SobolevPair p D U g :=
    fun D hD => (hSob D hD).congr (ae_restrict_of_ae hglobal) EventuallyEq.rfl
  have hUH : WeakPHarmonicPair p Kᶜ U g :=
    hH.congr_ae (ae_restrict_of_ae hglobal) EventuallyEq.rfl
  have hUunit : ∀ᵐ x ∂volume, 0≤U x ∧ U x≤1 := by
    filter_upwards [hglobal, hunit] with x hx hb
    rw [←hx]
    exact hb
  have hUlim : Tendsto (fun j => eLpNorm (φ j-U)
      (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume) atTop (𝓝 0) := by
    have he (j : ℕ) : eLpNorm (φ j-U) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume =
        eLpNorm (φ j-u) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume :=
      eLpNorm_congr_ae (EventuallyEq.rfl.sub hglobal.symm)
    simpa only [he] using hlu
  exact ⟨U, g, hUmem, hg, hUSob, hUcont, hUH, hUunit, hcap, φ, hφ, hUlim, hlg⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_continuous_exterior_variational_capacity_potential
