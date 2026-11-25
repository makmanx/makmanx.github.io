import SuperQuartic

/-! Strong local non-strict upper tests follow from the exact manuscript
strict-test bridge by an actual fourth-order perturbation with zero two-jet.
Only C1 regularity of the weak solution is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactPDE

theorem WeakPSubsolutionPair.viscosity_of_C1
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : WeakPSubsolutionPair p Ω u (gradient u))
    (hu : ContDiffOn ℝ 1 u Ω) (hn : 2≤n) :
    BMCompactAnalytic.IsViscosityPSubsolution p Ω u := by
  refine ⟨hw.1,hw.2.1,hu.continuousOn.upperSemicontinuousOn,?_⟩
  intro x hx φ hφ hv hupper hg
  have hex : ∃ U∈𝓝 x, ContDiffOn ℝ 2 φ U := hφ.contDiffOn le_rfl (by simp)
  obtain ⟨U,hUn,hφU⟩ := hex
  obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hUn
  obtain ⟨T,hTupper,hT,hxT⟩ := mem_nhds_iff.mp hupper
  let D : Set (Space n) := Ω ∩ V ∩ T
  have hD : IsOpen D := (hw.2.1.inter hV).inter hT
  have hxD : x∈D := ⟨⟨hx,hxV⟩,hxT⟩
  have hDΩ : D ⊆ Ω := inter_subset_left.trans inter_subset_left
  have hDU : D ⊆ U := (inter_subset_left.trans inter_subset_right).trans hVU
  have hlocal := (hw.mono hDΩ hD).manuscriptViscosity_of_C1 (hu.mono hDΩ) hn
  let ψ : Space n → ℝ := fun y => φ y+BMCompactAnalytic.strictContactQuartic x y
  have hq : ContDiff ℝ 2 (BMCompactAnalytic.strictContactQuartic x) :=
    (BMCompactAnalytic.contDiff_strictContactQuartic x).of_le (by decide)
  have hψ : ContDiffOn ℝ 2 ψ D := (hφU.mono hDU).add hq.contDiffOn
  have hval : u x=ψ x := by
    dsimp only [ψ]
    rw [BMCompactAnalytic.strictContactQuartic_self,add_zero]
    exact hv
  have hstrict : ∀ y∈D, y≠x → u y<ψ y := by
    intro y hy hyx
    have hle : u y≤φ y := hTupper hy.2
    have hpos := BMCompactAnalytic.strictContactQuartic_pos hyx
    dsimp only [ψ]
    linarith
  have hgrad : gradient ψ x≠0 := by
    simpa only [ψ,BMCompactAnalytic.gradient_add_strictContactQuartic_self
      (hφ.differentiableAt (by norm_num))] using hg
  have htest := hlocal.2.2.2 x hxD ψ hψ hval hstrict hgrad
  simpa only [ψ,BMCompactAnalytic.normalizedPLaplacian_add_strictContactQuartic_self p hφ] using htest

/-- Actual weak p-harmonicity plus C1 regularity implies the strong local
noncritical-test viscosity condition, without C2 regularity of u. -/
theorem IsWeakPHarmonic.viscosity_of_C1
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : IsWeakPHarmonic p Ω u) (hu : ContDiffOn ℝ 1 u Ω) (hn : 2≤n) :
    BMCompactAnalytic.IsViscosityPSubsolution p Ω u := by
  obtain ⟨g,hw⟩ := hw
  exact (hw.with_classical_gradient hu).subsolution.viscosity_of_C1 hu hn

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSubsolutionPair.viscosity_of_C1
#print axioms BMCompactPDE.IsWeakPHarmonic.viscosity_of_C1
