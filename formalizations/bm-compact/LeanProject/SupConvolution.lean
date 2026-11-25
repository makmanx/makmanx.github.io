import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
The actual supremal convolution of source equation (5.4), with the optimizing
fibre solved explicitly in one coordinate. Compact upper-level localization
proves maximum attainment and continuity; these properties are not hypotheses
of the main subcritical/negative-infinity results below.

This is the analytic envelope portion of printed Lemma 4.1 (label lem5.1).
It does not assert that the envelope satisfies a PDE, identify its top level
with a filled set, or prove the capacitary Brunn--Minkowski inequality.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Pointwise Topology

namespace BMCompactEnvelope

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def fibreValues (t : ℝ) (u v : V → ℝ) (x : V) : Set ℝ :=
  {r | ∃ y z : V, x = t • y + (1 - t) • z ∧ r = min (u y) (v z)}

/-- The actual supremum over all decompositions, not an arbitrary envelope. -/
def supConvolution (t : ℝ) (u v : V → ℝ) (x : V) : ℝ :=
  sSup (fibreValues t u v x)

def pairValue (t : ℝ) (u v : V → ℝ) (x y : V) : ℝ :=
  min (u y) (v ((1 - t)⁻¹ • (x - t • y)))

theorem solved_blend (t : ℝ) (h1 : 1 - t ≠ 0) (x y : V) :
    t • y + (1 - t) • ((1 - t)⁻¹ • (x - t • y)) = x := by
  rw [smul_smul, mul_inv_cancel₀ h1, one_smul]
  abel

theorem pairValue_blend (t : ℝ) (h1 : 1 - t ≠ 0) (u v : V → ℝ) (y z : V) :
    pairValue t u v (t • y + (1 - t) • z) y = min (u y) (v z) := by
  have heq : t • y + (1 - t) • z - t • y = (1 - t) • z := by abel
  simp only [pairValue, heq, smul_smul, inv_mul_cancel₀ h1, one_smul]

theorem pairValue_diagonal (t : ℝ) (h1 : 1 - t ≠ 0) (u v : V → ℝ) (x : V) :
    pairValue t u v x x = min (u x) (v x) := by
  have hblend : t • x + (1 - t) • x = x := by
    rw [← add_smul]
    simp
  simpa only [hblend] using pairValue_blend t h1 u v x x

theorem fibreValues_eq_range (t : ℝ) (h1 : 1 - t ≠ 0) (u v : V → ℝ) (x : V) :
    fibreValues t u v x = range (pairValue t u v x) := by
  ext r
  constructor
  · rintro ⟨y, z, hx, rfl⟩
    exact ⟨y, by rw [hx, pairValue_blend t h1]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, (1 - t)⁻¹ • (x - t • y), (solved_blend t h1 x y).symm, rfl⟩

theorem continuous_pairValue (t : ℝ) {u v : V → ℝ}
    (hu : Continuous u) (hv : Continuous v) : Continuous ↿(pairValue t u v) := by
  have hz : Continuous (fun q : V × V => (1 - t)⁻¹ • (q.1 - t • q.2)) :=
    (continuous_fst.sub (continuous_snd.const_smul t)).const_smul (1 - t)⁻¹
  exact (hu.comp continuous_snd).inf (hv.comp hz)

theorem sSup_range_of_global_max {f : V → ℝ} (y : V)
    (hy : ∀ z, f z ≤ f y) : sSup (range f) = f y := by
  apply le_antisymm
  · apply csSup_le (range_nonempty f)
    rintro _ ⟨z, rfl⟩
    exact hy z
  · exact le_csSup ⟨f y, by rintro _ ⟨z, rfl⟩; exact hy z⟩ (mem_range_self y)

theorem sSup_image_of_max {f : V → ℝ} {K : Set V} {y : V}
    (hy : y ∈ K) (hmax : ∀ z ∈ K, f z ≤ f y) : sSup (f '' K) = f y := by
  apply le_antisymm
  · apply csSup_le ⟨f y, mem_image_of_mem f hy⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hmax z hz
  · exact le_csSup ⟨f y, by rintro _ ⟨z, hz, rfl⟩; exact hmax z hz⟩
      (mem_image_of_mem f hy)

/-- A concrete compact upper level of u captures the entire optimizing fibre. -/
theorem exists_global_max_pairValue (t : ℝ) (h1 : 1 - t ≠ 0)
    {u v : V → ℝ} (hu : Continuous u) (hv : Continuous v) (x : V) (τ : ℝ)
    (hK : IsCompact {y | τ ≤ u y}) (hbase : τ ≤ min (u x) (v x)) :
    ∃ y : V, y ∈ {y | τ ≤ u y} ∧ ∀ z, pairValue t u v x z ≤ pairValue t u v x y := by
  have hxK : x ∈ {y | τ ≤ u y} := hbase.trans (min_le_left _ _)
  have hq : Continuous (pairValue t u v x) :=
    (continuous_pairValue t hu hv).comp (continuous_const.prodMk continuous_id)
  obtain ⟨y, hyK, hy⟩ := hK.exists_isMaxOn ⟨x, hxK⟩ hq.continuousOn
  refine ⟨y, hyK, ?_⟩
  intro z
  by_cases hz : τ ≤ u z
  · exact hy hz
  · apply le_of_lt
    calc
      pairValue t u v x z ≤ u z := min_le_left _ _
      _ < τ := lt_of_not_ge hz
      _ ≤ min (u x) (v x) := hbase
      _ = pairValue t u v x x := (pairValue_diagonal t h1 u v x).symm
      _ ≤ pairValue t u v x y := hy hxK

theorem supConvolution_eq_compact_sup (t : ℝ) (h1 : 1 - t ≠ 0)
    {u v : V → ℝ} (hu : Continuous u) (hv : Continuous v) (x : V) (τ : ℝ)
    (hK : IsCompact {y | τ ≤ u y}) (hbase : τ ≤ min (u x) (v x)) :
    supConvolution t u v x = sSup (pairValue t u v x '' {y | τ ≤ u y}) := by
  obtain ⟨y, hyK, hy⟩ := exists_global_max_pairValue t h1 hu hv x τ hK hbase
  rw [supConvolution, fibreValues_eq_range t h1,
    sSup_range_of_global_max y hy,
    sSup_image_of_max hyK (fun z _ => hy z)]

/-- An actual optimizing decomposition exists whenever a compact upper level
lies below the explicit diagonal competitor. -/
theorem exists_optimalPair_at_level (t : ℝ) (h1 : 1 - t ≠ 0)
    {u v : V → ℝ} (hu : Continuous u) (hv : Continuous v) (x : V) (τ : ℝ)
    (hK : IsCompact {y | τ ≤ u y}) (hbase : τ ≤ min (u x) (v x)) :
    ∃ y z : V, x = t • y + (1 - t) • z ∧
      supConvolution t u v x = min (u y) (v z) := by
  obtain ⟨y, _, hy⟩ := exists_global_max_pairValue t h1 hu hv x τ hK hbase
  refine ⟨y, (1 - t)⁻¹ • (x - t • y), (solved_blend t h1 x y).symm, ?_⟩
  change sSup (fibreValues t u v x) = pairValue t u v x y
  rw [fibreValues_eq_range t h1]
  exact sSup_range_of_global_max y hy

/-- Fixed compact localization gives true continuity at the point, not only
upper or lower semicontinuity. -/
theorem continuousAt_supConvolution_at_level (t : ℝ) (h1 : 1 - t ≠ 0)
    {u v : V → ℝ} (hu : Continuous u) (hv : Continuous v) (x : V) (τ : ℝ)
    (hK : IsCompact {y | τ ≤ u y}) (hbase : τ < min (u x) (v x)) :
    ContinuousAt (supConvolution t u v) x := by
  have hlocal : ∀ᶠ x' in 𝓝 x, τ < min (u x') (v x') :=
    (hu.inf hv).continuousAt.eventually (eventually_gt_nhds hbase)
  apply (hK.continuous_sSup (continuous_pairValue t hu hv)).continuousAt.congr
  filter_upwards [hlocal] with x' hx'
  exact (supConvolution_eq_compact_sup t h1 hu hv x' τ hK hx'.le).symm

section Proper
variable [ProperSpace V]

/-- Positive superlevels are compact for a continuous function decaying to0. -/
theorem isCompact_superlevel_of_tendsto_zero {u : V → ℝ} (hu : Continuous u)
    (hlim : Tendsto u (cobounded V) (𝓝 0)) {τ : ℝ} (hτ : 0 < τ) :
    IsCompact {y | τ ≤ u y} := by
  have he : ∀ᶠ y in cocompact V, u y < τ := by
    rw [← Metric.cobounded_eq_cocompact]
    exact hlim.eventually (eventually_lt_nhds hτ)
  obtain ⟨K, hK, hKu⟩ := hasBasis_cocompact.eventually_iff.1 he
  apply hK.of_isClosed_subset (isClosed_le continuous_const hu)
  intro y hy
  by_contra hyK
  exact (not_lt_of_ge hy) (hKu hyK)

/-- All upper levels are compact for a continuous function tending to−∞. -/
theorem isCompact_superlevel_of_tendsto_atBot {u : V → ℝ} (hu : Continuous u)
    (hlim : Tendsto u (cobounded V) atBot) (τ : ℝ) :
    IsCompact {y | τ ≤ u y} := by
  have he : ∀ᶠ y in cocompact V, u y < τ := by
    rw [← Metric.cobounded_eq_cocompact]
    exact hlim.eventually (eventually_lt_atBot τ)
  obtain ⟨K, hK, hKu⟩ := hasBasis_cocompact.eventually_iff.1 he
  apply hK.of_isClosed_subset (isClosed_le continuous_const hu)
  intro y hy
  by_contra hyK
  exact (not_lt_of_ge hy) (hKu hyK)

/-- Source Lemma4.1(a), subcritical analytic regime: optimizing pairs exist. -/
theorem exists_optimalPair_subcritical (t : ℝ) (h1 : 1 - t ≠ 0)
    {u v : V → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu0 : ∀ x, 0 < u x) (hv0 : ∀ x, 0 < v x)
    (hlim : Tendsto u (cobounded V) (𝓝 0)) (x : V) :
    ∃ y z : V, x = t • y + (1 - t) • z ∧
      supConvolution t u v x = min (u y) (v z) := by
  have hb : 0 < min (u x) (v x) := lt_min (hu0 x) (hv0 x)
  obtain ⟨τ, hτ, hτb⟩ := exists_between hb
  exact exists_optimalPair_at_level t h1 hu hv x τ
    (isCompact_superlevel_of_tendsto_zero hu hlim hτ) hτb.le

/-- Source Lemma4.1(b), actual continuity in the subcritical regime. -/
theorem continuous_supConvolution_subcritical (t : ℝ) (h1 : 1 - t ≠ 0)
    {u v : V → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu0 : ∀ x, 0 < u x) (hv0 : ∀ x, 0 < v x)
    (hlim : Tendsto u (cobounded V) (𝓝 0)) : Continuous (supConvolution t u v) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hb : 0 < min (u x) (v x) := lt_min (hu0 x) (hv0 x)
  obtain ⟨τ, hτ, hτb⟩ := exists_between hb
  exact continuousAt_supConvolution_at_level t h1 hu hv x τ
    (isCompact_superlevel_of_tendsto_zero hu hlim hτ) hτb

/-- Source Lemma4.1(a), critical/supercritical analytic regime. -/
theorem exists_optimalPair_atBot (t : ℝ) (h1 : 1 - t ≠ 0)
    {u v : V → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hlim : Tendsto u (cobounded V) atBot) (x : V) :
    ∃ y z : V, x = t • y + (1 - t) • z ∧
      supConvolution t u v x = min (u y) (v z) := by
  exact exists_optimalPair_at_level t h1 hu hv x (min (u x) (v x) - 1)
    (isCompact_superlevel_of_tendsto_atBot hu hlim _) (by linarith)

/-- Source Lemma4.1(b), continuity for functions tending to−∞. -/
theorem continuous_supConvolution_atBot (t : ℝ) (h1 : 1 - t ≠ 0)
    {u v : V → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hlim : Tendsto u (cobounded V) atBot) : Continuous (supConvolution t u v) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact continuousAt_supConvolution_at_level t h1 hu hv x (min (u x) (v x) - 1)
    (isCompact_superlevel_of_tendsto_atBot hu hlim _) (by linarith)

end Proper
end BMCompactEnvelope

#print axioms BMCompactEnvelope.exists_global_max_pairValue
#print axioms BMCompactEnvelope.supConvolution_eq_compact_sup
#print axioms BMCompactEnvelope.exists_optimalPair_at_level
#print axioms BMCompactEnvelope.continuousAt_supConvolution_at_level
#print axioms BMCompactEnvelope.isCompact_superlevel_of_tendsto_zero
#print axioms BMCompactEnvelope.isCompact_superlevel_of_tendsto_atBot
#print axioms BMCompactEnvelope.exists_optimalPair_subcritical
#print axioms BMCompactEnvelope.continuous_supConvolution_subcritical
#print axioms BMCompactEnvelope.exists_optimalPair_atBot
#print axioms BMCompactEnvelope.continuous_supConvolution_atBot
#print axioms BMCompactEnvelope.solved_blend
#print axioms BMCompactEnvelope.pairValue_blend
#print axioms BMCompactEnvelope.pairValue_diagonal
#print axioms BMCompactEnvelope.fibreValues_eq_range
#print axioms BMCompactEnvelope.continuous_pairValue
#print axioms BMCompactEnvelope.sSup_range_of_global_max
#print axioms BMCompactEnvelope.sSup_image_of_max
