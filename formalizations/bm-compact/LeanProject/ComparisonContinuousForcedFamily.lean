import ComparisonSelectedDirichlet
import NonlinearAnalyticBatch

/-! Actual selected positive-source approximants of a raw harmonic Sobolev
pair. Existence, interior continuity, pointwise ordering and monotonicity are
constructed. Genuine W0 corrections converge strongly in both Lp components.
Pointwise/uniform convergence, boundary continuity and C1 are not asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace BMCompactPDE

/-- The full continuous, pointwise ordered positive-forcing family is built
from actual weak harmonic data. The harmonic representative itself is selected
from the PDE and satisfies both signs of the local viscosity condition. -/
theorem WeakPHarmonicPair.exists_monotone_continuous_forced_approximants
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hH : WeakPHarmonicPair p Ω f gf) (hf : SobolevPair p Ω f gf)
    (hpn : p<(n : ℝ)) (hn : 2≤n) (hΩb : Bornology.IsBounded Ω) :
    ∃ F : Space n → ℝ,∃ u : ℕ → Space n → ℝ,∃ g : ℕ → Space n → Space n,
      ContinuousOn F Ω ∧ f =ᵐ[volume.restrict Ω] F ∧
      WeakPHarmonicPair p Ω F gf ∧
      BMCompactAnalytic.IsViscosityPSubsolution p Ω F ∧
      BMCompactAnalytic.IsViscosityPSubsolution p Ω (-F) ∧
      (∀ j,ContinuousOn (u j) Ω) ∧
      (∀ j,ZeroBoundarySobolevPair p Ω (u j-f) (g j-gf)) ∧
      (∀ j : ℕ,WeakPSourcePair p (((j : ℝ)+1)⁻¹) Ω (u j) (g j)) ∧
      (∀ j : ℕ,0<((j : ℝ)+1)⁻¹) ∧
      (∀ j,∀ x∈Ω,F x≤u j x) ∧
      (∀ x∈Ω,Antitone (fun j => u j x)) ∧
      Tendsto (fun j => eLpNorm (g j-gf) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (𝓝 0) ∧
      Tendsto (fun j => eLpNorm (u j-f) (ENNReal.ofReal p) (volume.restrict Ω))
        atTop (𝓝 0) := by
  obtain ⟨F,hFc,hfF,hHF,hVF,hVnegF⟩ :=
    hH.exists_continuous_two_sided_viscosity_representative hpn hn
  have hex (j : ℕ) := exists_unique_continuous_source_Dirichlet
    hH.1 hpn hn hH.2.1 hΩb (((j : ℝ)+1)⁻¹) hf
  choose u g huc hbu hu huniq using hex
  have hFzero : ZeroBoundarySobolevPair p Ω (F-f) (gf-gf) := by
    apply (zeroBoundarySobolevPair_zero hH.1 Ω).congr
    · filter_upwards [hfF] with x hx
      simp only [Pi.zero_apply,Pi.sub_apply,hx,sub_self]
    · exact Eventually.of_forall (fun x => by simp)
  have hpos (j : ℕ) : 0<((j : ℝ)+1)⁻¹ := inv_pos.mpr (by positivity)
  have hlower (j : ℕ) : ∀ x∈Ω,F x≤u j x :=
    hHF.source_zero.leOn_of_ordered_source_continuous_W0 (hu j) hf hFc (huc j)
      hFzero (hbu j) (hpos j).le hn hΩb
  have hantitone : ∀ x∈Ω,Antitone (fun j => u j x) := by
    intro x hx j k hjk
    have hsource : ((k : ℝ)+1)⁻¹≤((j : ℝ)+1)⁻¹ := by
      apply inv_anti₀ (by positivity)
      have hjkR : (j : ℝ)≤(k : ℝ) := by exact_mod_cast hjk
      linarith only [hjkR]
    exact (hu k).leOn_of_ordered_source_continuous_W0 (hu j) hf (huc k) (huc j)
      (hbu k) (hbu j) hsource hn hΩb x hx
  have hscal (j : ℕ) : f+(u j-f)=u j := by
    funext x
    simp only [Pi.add_apply,Pi.sub_apply]
    ring
  have hgrad (j : ℕ) : gf+(g j-gf)=g j := by
    funext x
    simp only [Pi.add_apply,Pi.sub_apply]
    abel
  have huadd (j : ℕ) : WeakPSourcePair p (((j : ℝ)+1)⁻¹) Ω
      (f+(u j-f)) (gf+(g j-gf)) := by
    simpa only [hscal,hgrad] using hu j
  have hc : Tendsto (fun j : ℕ => ((j : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  obtain ⟨hg,hw⟩ := hH.forced_family_W1p_tendsto_allp hf hpn hΩb hbu huadd hc
  exact ⟨F,u,g,hFc,hfF,hHF,hVF,hVnegF,huc,hbu,hu,hpos,hlower,hantitone,hg,hw⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.exists_monotone_continuous_forced_approximants
