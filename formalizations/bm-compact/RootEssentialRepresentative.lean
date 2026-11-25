import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! Representative selection from an explicit vanishing a.e. oscillation input.
This file does NOT derive that input from a weak PDE and does not assert C1.
The representative is a limit along the genuine neighborhood/a.e. filter;
no continuous representative, global integrability or pointwise values of the
raw measurable representative are assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace BMCompactRepresentative
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]

def essentialFilter (x : X) : Filter X := 𝓝 x ⊓ ae μ

def essentialRepresentative (u : X → ℝ) (x : X) : ℝ :=
  Filter.limUnder (essentialFilter μ x) u

def VanishingEssentialOscillation (u : X → ℝ) (Ω : Set X) : Prop :=
  ∀ x ∈ Ω, ∀ ε : ℝ, 0 < ε → ∃ U : Set X, ∃ a : ℝ,
    IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      ∀ᵐ y ∂μ.restrict U, dist (u y) a ≤ ε

theorem essentialFilter_neBot (x : X) : (essentialFilter μ x).NeBot := by
  apply Filter.inf_neBot_iff.mpr
  intro s hs t ht
  obtain ⟨U,hUs,hUo,hxU⟩ := mem_nhds_iff.mp hs
  have hUμ : μ U ≠ 0 := hUo.measure_ne_zero μ ⟨x,hxU⟩
  letI : (ae (μ.restrict U)).NeBot := ae_restrict_neBot.mpr hUμ
  have ha : ∀ᵐ y ∂μ.restrict U, y ∈ U ∧ y ∈ t :=
    (show ∀ᵐ y ∂μ.restrict U, y ∈ U from self_mem_ae_restrict hUo.measurableSet).and
      (ae_restrict_of_ae ht)
  obtain ⟨y,hyU,hyt⟩ := ha.exists
  exact ⟨y,hUs hyU,hyt⟩

private theorem eventually_essential_of_ae_open {u : X → ℝ} {x : X}
    {U : Set X} {a ε : ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (hu : ∀ᵐ y ∂μ.restrict U, dist (u y) a ≤ ε) :
    ∀ᶠ y in essentialFilter μ x, dist (u y) a ≤ ε := by
  have ha : ∀ᵐ y ∂μ, y ∈ U → dist (u y) a ≤ ε :=
    (ae_restrict_iff' hU.measurableSet).mp hu
  have hb : ∀ᶠ y in essentialFilter μ x, y ∈ U :=
    (show ∀ᶠ y in 𝓝 x, y ∈ U from hU.mem_nhds hx).filter_mono inf_le_left
  have hc : ∀ᶠ y in essentialFilter μ x, y ∈ U → dist (u y) a ≤ ε :=
    ha.filter_mono inf_le_right
  filter_upwards [hb,hc] with y hy hya using hya hy

theorem cauchy_essentialMap {u : X → ℝ} {Ω : Set X}
    (hu : VanishingEssentialOscillation μ u Ω) {x : X} (hx : x ∈ Ω) :
    Cauchy (Filter.map u (essentialFilter μ x)) := by
  letI := essentialFilter_neBot μ x
  apply Metric.cauchy_iff.mpr
  refine ⟨inferInstance,?_⟩
  intro ε hε
  obtain ⟨U,a,hU,hxU,-,ha⟩ := hu x hx (ε/4) (by linarith)
  refine ⟨{z : ℝ | dist z a ≤ ε/4},?_,?_⟩
  · exact Filter.mem_map.mpr (eventually_essential_of_ae_open μ hU hxU ha)
  · intro z hz w hw
    have hd := dist_triangle z a w
    rw [dist_comm a w] at hd
    change dist z a ≤ ε/4 at hz
    change dist w a ≤ ε/4 at hw
    linarith

theorem tendsto_essentialRepresentative {u : X → ℝ} {Ω : Set X}
    (hu : VanishingEssentialOscillation μ u Ω) {x : X} (hx : x ∈ Ω) :
    Tendsto u (essentialFilter μ x) (𝓝 (essentialRepresentative μ u x)) := by
  letI := essentialFilter_neBot μ x
  exact tendsto_nhds_limUnder ((cauchy_map_iff_exists_tendsto.mp
    (cauchy_essentialMap μ hu hx)))

private theorem representative_dist_le_center {u : X → ℝ} {Ω U : Set X}
    (hu : VanishingEssentialOscillation μ u Ω) {x : X} (hx : x ∈ Ω)
    (hU : IsOpen U) (hxU : x ∈ U) {a ε : ℝ}
    (ha : ∀ᵐ y ∂μ.restrict U, dist (u y) a ≤ ε) :
    dist (essentialRepresentative μ u x) a ≤ ε := by
  letI := essentialFilter_neBot μ x
  exact le_of_tendsto ((tendsto_essentialRepresentative μ hu hx).dist tendsto_const_nhds)
    (eventually_essential_of_ae_open μ hU hxU ha)

theorem continuousOn_essentialRepresentative {u : X → ℝ} {Ω : Set X}
    (hu : VanishingEssentialOscillation μ u Ω) :
    ContinuousOn (essentialRepresentative μ u) Ω := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨U,a,hU,hxU,hUΩ,ha⟩ := hu x hx (ε/4) (by linarith)
  have hxa := representative_dist_le_center μ hu hx hU hxU ha
  have hUev : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hxU
  filter_upwards [hUev] with y hy
  have hya := representative_dist_le_center μ hu (hUΩ hy) hU hy ha
  have hd := dist_triangle (essentialRepresentative μ u y) a
    (essentialRepresentative μ u x)
  rw [dist_comm a (essentialRepresentative μ u x)] at hd
  exact hd.trans_lt (by linarith)

private theorem local_ae_dist_representative {u : X → ℝ} {Ω : Set X}
    (hu : VanishingEssentialOscillation μ u Ω) {x : X} (hx : x ∈ Ω)
    {ε : ℝ} (hε : 0 < ε) : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      ∀ᵐ y ∂μ.restrict U, dist (u y) (essentialRepresentative μ u y) ≤ ε := by
  obtain ⟨U,a,hU,hxU,hUΩ,ha⟩ := hu x hx (ε/2) (by linarith)
  refine ⟨U,hU,hxU,hUΩ,?_⟩
  filter_upwards [ha,self_mem_ae_restrict hU.measurableSet] with y hya hyU
  have hva := representative_dist_le_center μ hu (hUΩ hyU) hU hyU ha
  have hd := dist_triangle (u y) a (essentialRepresentative μ u y)
  rw [dist_comm a (essentialRepresentative μ u y)] at hd
  linarith

private theorem ae_dist_representative_le [SecondCountableTopology X]
    {u : X → ℝ} {Ω : Set X} (hu : VanishingEssentialOscillation μ u Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ y ∂μ.restrict Ω, dist (u y) (essentialRepresentative μ u y) ≤ ε := by
  classical
  have hex (x : Ω) := local_ae_dist_representative μ hu x.2 hε
  choose U hU using hex
  have hn (x : X) (hx : x ∈ Ω) : U ⟨x,hx⟩ ∈ 𝓝[Ω] x :=
    mem_nhdsWithin_of_mem_nhds ((hU ⟨x,hx⟩).1.mem_nhds (hU ⟨x,hx⟩).2.1)
  let V : X → Set X := fun x => if hx : x ∈ Ω then U ⟨x,hx⟩ else univ
  have hV (x : X) (hx : x ∈ Ω) : V x ∈ 𝓝[Ω] x := by simpa [V,hx] using hn x hx
  obtain ⟨t,htΩ,htc,hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin hV
  have hall : ∀ᵐ y ∂μ.restrict (⋃ x ∈ t, V x),
      dist (u y) (essentialRepresentative μ u y) ≤ ε := by
    apply (ae_restrict_biUnion_iff V htc _).mpr
    intro x hx
    simpa [V,htΩ hx] using (hU ⟨x,htΩ hx⟩).2.2.2
  exact ae_restrict_of_ae_restrict_of_subset hcover hall

theorem ae_eq_essentialRepresentative [SecondCountableTopology X]
    {u : X → ℝ} {Ω : Set X} (hu : VanishingEssentialOscillation μ u Ω) :
    u =ᵐ[μ.restrict Ω] essentialRepresentative μ u := by
  have hb (n : ℕ) : ∀ᵐ y ∂μ.restrict Ω,
      dist (u y) (essentialRepresentative μ u y) ≤ 1/((n : ℝ)+1) :=
    ae_dist_representative_le μ hu (by positivity)
  filter_upwards [ae_all_iff.mpr hb] with y hy
  apply dist_eq_zero.mp
  apply le_antisymm ?_ dist_nonneg
  exact ge_of_tendsto' (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hy

theorem exists_unique_continuousRepresentative [SecondCountableTopology X]
    {u : X → ℝ} {Ω : Set X} (hΩ : IsOpen Ω)
    (hu : VanishingEssentialOscillation μ u Ω) :
    ∃ v : X → ℝ, ContinuousOn v Ω ∧ u =ᵐ[μ.restrict Ω] v ∧
      ∀ w : X → ℝ, ContinuousOn w Ω → u =ᵐ[μ.restrict Ω] w → EqOn v w Ω := by
  refine ⟨essentialRepresentative μ u,continuousOn_essentialRepresentative μ hu,
    ae_eq_essentialRepresentative μ hu,?_⟩
  intro w hw huw
  exact Measure.eqOn_open_of_ae_eq ((ae_eq_essentialRepresentative μ hu).symm.trans huw)
    hΩ (continuousOn_essentialRepresentative μ hu) hw

end BMCompactRepresentative

#print axioms BMCompactRepresentative.essentialFilter_neBot
#print axioms BMCompactRepresentative.cauchy_essentialMap
#print axioms BMCompactRepresentative.tendsto_essentialRepresentative
#print axioms BMCompactRepresentative.continuousOn_essentialRepresentative
#print axioms BMCompactRepresentative.ae_eq_essentialRepresentative
#print axioms BMCompactRepresentative.exists_unique_continuousRepresentative
