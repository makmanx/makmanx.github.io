import UpstreamCriticalContinuity
import ComparisonSelectedDirichlet

/-! Actual bounded-domain source Dirichlet construction with selected interior
continuity for every p>1,n>=2. The true W0 boundary correction and scalar
uniqueness are retained. This does not assert pointwise boundary continuity.
The viscosity predicates below are the existing noncritical-test predicates;
general critical-point comparison remains a separate obligation. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE
theorem exists_unique_continuous_source_Dirichlet_allp
    {n : ℕ} {p : ℝ} (hp : 1<p) (hn : 2≤n)
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
  obtain ⟨u,huc,hae,hu⟩ := hs.exists_continuous_weak_representative_allp hn
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


theorem WeakPHarmonicPair.exists_continuous_two_sided_viscosity_representative_allp
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {g : Space n → Space n} (hu : WeakPHarmonicPair p Ω u g) (hn : 2≤n) :
    ∃ v : Space n → ℝ,ContinuousOn v Ω ∧ u =ᵐ[volume.restrict Ω] v ∧
      WeakPHarmonicPair p Ω v g ∧
      BMCompactAnalytic.IsViscosityPSubsolution p Ω v ∧
      BMCompactAnalytic.IsViscosityPSubsolution p Ω (-v) := by
  obtain ⟨v,hvc,hae,hv⟩ := hu.source_zero.exists_continuous_weak_representative_allp hn
  have hH := hv.harmonic_of_source_zero
  have hV : IsWeakPHarmonic p Ω v := ⟨g,hH⟩
  have hneg : IsWeakPHarmonic p Ω (-v) := by
    simpa only [neg_one_smul] using hV.smul (-1)
  exact ⟨v,hvc,hae,hH,hV.viscosity_of_continuous hvc hn,
    hneg.viscosity_of_continuous hvc.neg hn⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_unique_continuous_source_Dirichlet_allp
#print axioms BMCompactPDE.WeakPHarmonicPair.exists_continuous_two_sided_viscosity_representative_allp
