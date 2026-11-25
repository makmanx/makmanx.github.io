import UpstreamBoundaryTrace

/-! Actual unit-boundary continuous variational potentials under an explicit
analytic smooth-barrier-family condition. The condition supplies actual
functions/PDEs and their scalar normalization, not the desired potential trace
or comparison. The full original global variational data are retained. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem exists_continuous_unit_variational_capacity_potential_of_smooth_barriers
    {n : ℕ} {p : ℝ} (hp : 1<p) (hpn : p<(n:ℝ)) {K : Set (Space n)} (hK : IsCompact K)
    (hbarrier : ∀ a∈K,∃ B : ℕ → Space n → ℝ,
      (∀ j,ContDiff ℝ ∞ (B j)) ∧ (∀ j x,x∈K → B j x≤1) ∧
      (∀ j,WeakPHarmonicPair p Kᶜ (B j) (gradient (B j))) ∧
      (∀ j,Tendsto (B j) (cocompact (Space n)) (𝓝 0)) ∧
      Tendsto (fun j=>B j a) atTop (𝓝 1)) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      Continuous u ∧ (∀ x∈K,u x=1) ∧
      MemLp u (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume ∧
      MemLp g (ENNReal.ofReal p) volume ∧
      (∀ D : Set (Space n),Bornology.IsBounded D → SobolevPair p D u g) ∧
      WeakPHarmonicPair p Kᶜ u g ∧ (∀ x,0≤u x ∧ u x≤1) ∧
      Tendsto u (cocompact (Space n)) (𝓝 0) ∧
      BMCompactCapacityV2.relativeCapacity p K univ=ENNReal.ofReal (∫ x,‖g x‖^p ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K univ (φ j)) ∧
        Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume) atTop (𝓝 0) ∧
        Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  obtain ⟨u,g,hu,hg,hSob,hcont,hH,hpoint,hinfty,hunit,hcap,φ,hφ,hlu,hlg⟩ :=
    exists_continuous_exterior_capacity_potential_vanishing_at_infinity hp hpn hK
  have hn1 : 1<n := by exact_mod_cast (hp.trans hpn)
  have hn : 2≤n := Nat.succ_le_iff.mpr hn1
  have hpq : p≤(n:ℝ)*p/((n:ℝ)-p) := by
    apply (le_div_iff₀ (sub_pos.mpr hpn)).mpr
    nlinarith [sq_nonneg p]
  obtain ⟨v,hvc,hvae,hvK,hvout,-⟩ :=
    hH.exists_continuous_unit_extension_of_smooth_barriers hK hn hpq hcont hSob hu hunit
      (fun x hx=>(hpoint x hx).2) hφ hlu hlg hbarrier
  have hvmem : MemLp v (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume :=
    (memLp_congr_ae hvae.symm).mp hu
  have hvSob : ∀ D : Set (Space n),Bornology.IsBounded D → SobolevPair p D v g :=
    fun D hD=>(hSob D hD).congr (ae_restrict_of_ae hvae.symm) EventuallyEq.rfl
  have hvH : WeakPHarmonicPair p Kᶜ v g :=
    hH.congr_ae (ae_restrict_of_ae hvae.symm) EventuallyEq.rfl
  have hvbound (x : Space n) : 0≤v x ∧ v x≤1 := by
    by_cases hx : x∈K
    · rw [hvK x hx]
      exact ⟨zero_le_one,le_rfl⟩
    · rw [hvout x hx]
      exact hpoint x hx
  have hvlim : Tendsto v (cocompact (Space n)) (𝓝 0) := by
    apply hinfty.congr'
    filter_upwards [hK.compl_mem_cocompact] with x hx
    exact (hvout x hx).symm
  have hvapprox : Tendsto (fun j=>eLpNorm (φ j-v) (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume) atTop (𝓝 0) := by
    have heq (j : ℕ) : eLpNorm (φ j-v) (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume=
        eLpNorm (φ j-u) (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume :=
      eLpNorm_congr_ae (EventuallyEq.rfl.sub hvae)
    simpa only [heq] using hlu
  exact ⟨v,g,hvc,hvK,hvmem,hg,hvSob,hvH,hvbound,hvlim,hcap,φ,hφ,hvapprox,hlg⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_continuous_unit_variational_capacity_potential_of_smooth_barriers
