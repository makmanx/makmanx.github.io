import RootAllpDirichlet
import RootSourceContinuity
import SuperContinuousBatch
import WeakHarmonicScaling

/-! Constructed continuous representatives of actual source Dirichlet solutions,
with their original genuine W0 data retained. Continuity is derived from the
weak PDE at 1<p<n; no pointwise boundary value, boundary continuity or C1
regularity is asserted. Pointwise source order follows from actual weak order.
The source-zero endpoint also gives both signs of the local noncritical-test
viscosity condition without assuming a continuous representative as input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem comparison_sobolev_of_boundary_correction
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {f u : Space n → ℝ} {gf g : Space n → Space n}
    (hf : SobolevPair p Ω f gf)
    (hb : ZeroBoundarySobolevPair p Ω (u-f) (g-gf)) :
    SobolevPair p Ω u g := by
  apply (hf.add hb.1).congr
  · exact Eventually.of_forall (fun x => by simp only [Pi.add_apply,Pi.sub_apply]; ring)
  · exact Eventually.of_forall (fun x => by simp only [Pi.add_apply,Pi.sub_apply]; abel)

private theorem comparison_continuous_le_of_ae
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u v : Space n → ℝ} (hu : ContinuousOn u Ω) (hv : ContinuousOn v Ω)
    (hae : ∀ᵐ x ∂volume.restrict Ω,u x≤v x) :
    ∀ x∈Ω,u x≤v x := by
  have hmax : (fun x => max (u x) (v x)) =ᵐ[volume.restrict Ω] v :=
    hae.mono (fun _ hx => max_eq_right hx)
  have he := Measure.eqOn_open_of_ae_eq hmax hΩ (hu.sup hv) hv
  intro x hx
  exact (le_max_left _ _).trans (he hx).le

/-- Genuine source ordering for the continuous representatives of two actual
weak solutions with the same Sobolev Dirichlet datum. -/
theorem WeakPSourcePair.leOn_of_ordered_source_continuous_W0
    {n : ℕ} {p c d : ℝ} {Ω : Set (Space n)}
    {f u v : Space n → ℝ} {gf g h : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hv : WeakPSourcePair p d Ω v h)
    (hf : SobolevPair p Ω f gf)
    (huc : ContinuousOn u Ω) (hvc : ContinuousOn v Ω)
    (hbu : ZeroBoundarySobolevPair p Ω (u-f) (g-gf))
    (hbv : ZeroBoundarySobolevPair p Ω (v-f) (h-gf))
    (hcd : c≤d) (hn : 2≤n) (hΩb : Bornology.IsBounded Ω) :
    ∀ x∈Ω,u x≤v x := by
  have hboundary : ZeroBoundarySobolevPair p Ω (u-v) (g-h) := by
    apply (hbu.sub_actual hbv).congr
    · exact Eventually.of_forall (fun x => by simp only [Pi.sub_apply]; ring)
    · exact Eventually.of_forall (fun x => by simp only [Pi.sub_apply]; abel)
  have hae := hu.ae_le_of_ordered_source_W0 hv hcd hn hΩb
    (comparison_sobolev_of_boundary_correction hf hbu)
    (comparison_sobolev_of_boundary_correction hf hbv) hboundary
  exact comparison_continuous_le_of_ae hu.2.1 huc hvc hae

/-- A continuous representative is constructed from arbitrary actual Sobolev
Dirichlet data. The correction remains genuinely W0, and the continuous scalar
is unique on the open domain among actual solutions with the same datum. -/
theorem exists_unique_continuous_source_Dirichlet
    {n : ℕ} {p : ℝ} (hp : 1<p) (hpn : p<(n : ℝ)) (hn : 2≤n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (c : ℝ) {f : Space n → ℝ} {gf : Space n → Space n}
    (hf : SobolevPair p Ω f gf) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      ContinuousOn u Ω ∧ ZeroBoundarySobolevPair p Ω (u-f) (g-gf) ∧
      WeakPSourcePair p c Ω u g ∧
      ∀ (v : Space n → ℝ) (h : Space n → Space n),
        ContinuousOn v Ω → ZeroBoundarySobolevPair p Ω (v-f) (h-gf) →
        WeakPSourcePair p c Ω v h → EqOn u v Ω := by
  obtain ⟨w,gw,hw,hs⟩ := exists_weak_source_Dirichlet_allp hp hn hΩ hΩb c hf
  obtain ⟨u,huc,hae,hu⟩ := hs.exists_continuous_weak_representative hpn
  have hb : ZeroBoundarySobolevPair p Ω (u-f) ((gf+gw)-gf) := by
    apply hw.congr
    · filter_upwards [hae] with x hx
      change f x+w x=u x at hx
      change w x=u x-f x
      linarith only [hx]
    · exact Eventually.of_forall (fun x => by simp only [Pi.add_apply,Pi.sub_apply]; abel)
  refine ⟨u,gf+gw,huc,hb,hu,?_⟩
  intro v h hvc hbv hv
  have huv := hu.leOn_of_ordered_source_continuous_W0 hv hf huc hvc hb hbv
    le_rfl hn hΩb
  have hvu := hv.leOn_of_ordered_source_continuous_W0 hu hf hvc huc hbv hb
    le_rfl hn hΩb
  exact fun x hx => le_antisymm (huv x hx) (hvu x hx)

private theorem comparison_two_sided_viscosity_of_continuous_harmonic
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {g : Space n → Space n} (hu : WeakPHarmonicPair p Ω u g)
    (huc : ContinuousOn u Ω) (hn : 2≤n) :
    BMCompactAnalytic.IsViscosityPSubsolution p Ω u ∧
      BMCompactAnalytic.IsViscosityPSubsolution p Ω (-u) := by
  have hnegative : IsWeakPHarmonic p Ω (-u) := by
    have h := (show IsWeakPHarmonic p Ω u from ⟨g,hu⟩).smul (-1)
    simpa only [neg_one_smul] using h
  exact ⟨(show IsWeakPHarmonic p Ω u from ⟨g,hu⟩).viscosity_of_continuous huc hn,
    hnegative.viscosity_of_continuous huc.neg hn⟩

/-- An actual raw weak harmonic pair determines a continuous representative
satisfying both signs of the local viscosity condition. No C0/C1 hypothesis is
made about the supplied raw function. Equality outside the domain is irrelevant. -/
theorem WeakPHarmonicPair.exists_continuous_two_sided_viscosity_representative
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {g : Space n → Space n} (hu : WeakPHarmonicPair p Ω u g)
    (hpn : p<(n : ℝ)) (hn : 2≤n) :
    ∃ v : Space n → ℝ,ContinuousOn v Ω ∧ u =ᵐ[volume.restrict Ω] v ∧
      WeakPHarmonicPair p Ω v g ∧
      BMCompactAnalytic.IsViscosityPSubsolution p Ω v ∧
      BMCompactAnalytic.IsViscosityPSubsolution p Ω (-v) := by
  obtain ⟨v,hvc,hae,hv⟩ := hu.source_zero.exists_continuous_weak_representative hpn
  have hH := hv.harmonic_of_source_zero
  exact ⟨v,hvc,hae,hH,comparison_two_sided_viscosity_of_continuous_harmonic hH hvc hn⟩

/-- A genuine harmonic Dirichlet solution and both signs of its viscosity
condition are constructed from arbitrary Sobolev data, retaining W0 attainment. -/
theorem exists_continuous_harmonic_viscosity_Dirichlet
    {n : ℕ} {p : ℝ} (hp : 1<p) (hpn : p<(n : ℝ)) (hn : 2≤n)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hf : SobolevPair p Ω f gf) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      ContinuousOn u Ω ∧ ZeroBoundarySobolevPair p Ω (u-f) (g-gf) ∧
      WeakPHarmonicPair p Ω u g ∧
      BMCompactAnalytic.IsViscosityPSubsolution p Ω u ∧
      BMCompactAnalytic.IsViscosityPSubsolution p Ω (-u) := by
  obtain ⟨u,g,huc,hb,hu,-⟩ := exists_unique_continuous_source_Dirichlet hp hpn hn hΩ hΩb 0 hf
  have hH := hu.harmonic_of_source_zero
  exact ⟨u,g,huc,hb,hH,comparison_two_sided_viscosity_of_continuous_harmonic hH huc hn⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.leOn_of_ordered_source_continuous_W0
#print axioms BMCompactPDE.exists_unique_continuous_source_Dirichlet
#print axioms BMCompactPDE.WeakPHarmonicPair.exists_continuous_two_sided_viscosity_representative
#print axioms BMCompactPDE.exists_continuous_harmonic_viscosity_Dirichlet
