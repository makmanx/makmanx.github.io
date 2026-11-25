import SupConvolution

/-!
Exact envelope bounds, superlevel geometry and decay for the supremum over
actual weighted decompositions. These are the functional parts of source
Lemma4.1 (lem5.1), not a p-Laplace comparison principle.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Pointwise Topology

namespace BMCompactEnvelope
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem fibreValues_nonempty (t : ℝ) (u v : V → ℝ) (x : V) :
    (fibreValues t u v x).Nonempty := by
  refine ⟨min (u x) (v x), x, x, ?_, rfl⟩
  rw [← add_smul]
  simp

theorem bddAbove_fibreValues_of_bound (t : ℝ) {u v : V → ℝ} {m : ℝ}
    (hu : ∀ y, u y ≤ m) (x : V) : BddAbove (fibreValues t u v x) := by
  refine ⟨m, ?_⟩
  rintro r ⟨y, z, _, rfl⟩
  exact (min_le_left _ _).trans (hu y)

/-- Every genuine decomposition supplies a lower bound for the envelope. -/
theorem min_le_supConvolution_of_decomposition (t : ℝ)
    {u v : V → ℝ} {m : ℝ} (hu : ∀ y, u y ≤ m) {x y z : V}
    (hx : x = t • y + (1 - t) • z) : min (u y) (v z) ≤ supConvolution t u v x :=
  le_csSup (bddAbove_fibreValues_of_bound t hu x) ⟨y, z, hx, rfl⟩

/-- Source (5.6)(b): the actual supremum lies between the diagonal minimum
and the common upper bound. -/
theorem supConvolution_bounds (t : ℝ) {u v : V → ℝ} {m : ℝ}
    (hu : ∀ y, u y ≤ m) (x : V) :
    min (u x) (v x) ≤ supConvolution t u v x ∧ supConvolution t u v x ≤ m := by
  constructor
  · apply min_le_supConvolution_of_decomposition t hu
    rw [← add_smul]
    simp
  · apply csSup_le (fibreValues_nonempty t u v x)
    rintro r ⟨y, z, _, rfl⟩
    exact (min_le_left _ _).trans (hu y)

/-- When the supremum is attained, its superlevel points are exactly the
weighted combinations of the two component superlevel points. -/
theorem supConvolution_superlevel_eq_of_attained (t : ℝ)
    {u v : V → ℝ} {m : ℝ} (hu : ∀ y, u y ≤ m)
    (hatt : ∀ x, ∃ y z : V, x = t • y + (1 - t) • z ∧
      supConvolution t u v x = min (u y) (v z)) (a : ℝ) :
    {x | a ≤ supConvolution t u v x} =
      t • {y | a ≤ u y} + (1 - t) • {z | a ≤ v z} := by
  ext x
  constructor
  · intro hx
    change a ≤ supConvolution t u v x at hx
    obtain ⟨y, z, hxyz, hval⟩ := hatt x
    rw [hval] at hx
    obtain ⟨hy, hz⟩ := le_min_iff.mp hx
    exact ⟨t • y, ⟨y, hy, rfl⟩, (1 - t) • z, ⟨z, hz, rfl⟩, hxyz.symm⟩
  · rintro ⟨a', ⟨y, hy, rfl⟩, b', ⟨z, hz, rfl⟩, hxyz⟩
    exact (le_min hy hz).trans
      (min_le_supConvolution_of_decomposition t hu hxyz.symm)

/-- The first equality in source (5.6)(c), expressed directly for the maximum
level sets. Identifying these sets with fillings is a separate PDE/topology step. -/
theorem supConvolution_top_level_eq_of_attained (t : ℝ)
    {u v : V → ℝ} {m : ℝ} (hu : ∀ y, u y ≤ m) (hv : ∀ z, v z ≤ m)
    (hatt : ∀ x, ∃ y z : V, x = t • y + (1 - t) • z ∧
      supConvolution t u v x = min (u y) (v z)) :
    {x | supConvolution t u v x = m} =
      t • {y | u y = m} + (1 - t) • {z | v z = m} := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, z, hxyz, hval⟩ := hatt x
    rw [hx] at hval
    have hboth := le_min_iff.mp hval.le
    have hy : u y = m := le_antisymm (hu y) hboth.1
    have hz : v z = m := le_antisymm (hv z) hboth.2
    exact ⟨t • y, ⟨y, hy, rfl⟩, (1 - t) • z, ⟨z, hz, rfl⟩, hxyz.symm⟩
  · rintro ⟨a', ⟨y, hy, rfl⟩, b', ⟨z, hz, rfl⟩, hxyz⟩
    apply le_antisymm (supConvolution_bounds t hu x).2
    change u y = m at hy
    change v z = m at hz
    have hmin := min_le_supConvolution_of_decomposition t (v := v) hu hxyz.symm
    simpa only [hy, hz, min_self] using hmin

section Proper
variable [ProperSpace V]

/-- Actual subcritical superlevel identity: attainment is derived from decay
and positivity, not assumed as an envelope axiom. -/
theorem supConvolution_superlevel_eq_subcritical (t : ℝ) (h1 : 1 - t ≠ 0)
    {u v : V → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu0 : ∀ x, 0 < u x) (hv0 : ∀ x, 0 < v x)
    (hlim : Tendsto u (cobounded V) (𝓝 0)) {m : ℝ} (hub : ∀ x, u x ≤ m)
    (a : ℝ) :
    {x | a ≤ supConvolution t u v x} =
      t • {y | a ≤ u y} + (1 - t) • {z | a ≤ v z} :=
  supConvolution_superlevel_eq_of_attained t hub
    (exists_optimalPair_subcritical t h1 hu hv hu0 hv0 hlim) a

/-- Source subcritical decay, proved by compact superlevel geometry. -/
theorem tendsto_supConvolution_zero (t : ℝ) (h1 : 1 - t ≠ 0)
    {u v : V → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu0 : ∀ x, 0 < u x) (hv0 : ∀ x, 0 < v x)
    (hulim : Tendsto u (cobounded V) (𝓝 0))
    (hvlim : Tendsto v (cobounded V) (𝓝 0))
    {m : ℝ} (hub : ∀ x, u x ≤ m) :
    Tendsto (supConvolution t u v) (cobounded V) (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun x =>
      ha.trans ((lt_min (hu0 x) (hv0 x)).trans_le (supConvolution_bounds t hub x).1))
  · intro b hb
    let K : Set V := t • {y | b ≤ u y} + (1 - t) • {z | b ≤ v z}
    have hK : IsCompact K :=
      ((isCompact_superlevel_of_tendsto_zero hu hulim hb).smul t).add
        ((isCompact_superlevel_of_tendsto_zero hv hvlim hb).smul (1 - t))
    have he : ∀ᶠ x in cobounded V, x ∉ K := by
      rw [Metric.cobounded_eq_cocompact]
      exact hK.compl_mem_cocompact
    filter_upwards [he] with x hx
    apply lt_of_not_ge
    intro hbx
    have hmem : x ∈ {x | b ≤ supConvolution t u v x} := hbx
    rw [supConvolution_superlevel_eq_subcritical t h1 hu hv hu0 hv0 hulim hub b] at hmem
    exact hx hmem

/-- The critical/supercritical negative envelope itself tends to−∞. The
stronger source estimate w*−theta*w→−∞ needs the radial growth comparison. -/
theorem tendsto_supConvolution_atBot (t : ℝ) (h1 : 1 - t ≠ 0)
    {u v : V → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hulim : Tendsto u (cobounded V) atBot)
    (hvlim : Tendsto v (cobounded V) atBot)
    {m : ℝ} (hub : ∀ x, u x ≤ m) :
    Tendsto (supConvolution t u v) (cobounded V) atBot := by
  apply tendsto_atBot.2
  intro b
  let K : Set V := t • {y | b ≤ u y} + (1 - t) • {z | b ≤ v z}
  have hK : IsCompact K :=
    ((isCompact_superlevel_of_tendsto_atBot hu hulim b).smul t).add
      ((isCompact_superlevel_of_tendsto_atBot hv hvlim b).smul (1 - t))
  have he : ∀ᶠ x in cobounded V, x ∉ K := by
    rw [Metric.cobounded_eq_cocompact]
    exact hK.compl_mem_cocompact
  filter_upwards [he] with x hx
  apply le_of_lt
  apply lt_of_not_ge
  intro hbx
  have hmem : x ∈ {x | b ≤ supConvolution t u v x} := hbx
  rw [supConvolution_superlevel_eq_of_attained t hub
    (exists_optimalPair_atBot t h1 hu hv hulim) b] at hmem
  exact hx hmem

end Proper
end BMCompactEnvelope

#print axioms BMCompactEnvelope.fibreValues_nonempty
#print axioms BMCompactEnvelope.bddAbove_fibreValues_of_bound
#print axioms BMCompactEnvelope.min_le_supConvolution_of_decomposition
#print axioms BMCompactEnvelope.supConvolution_bounds
#print axioms BMCompactEnvelope.supConvolution_superlevel_eq_of_attained
#print axioms BMCompactEnvelope.supConvolution_top_level_eq_of_attained
#print axioms BMCompactEnvelope.supConvolution_superlevel_eq_subcritical
#print axioms BMCompactEnvelope.tendsto_supConvolution_zero
#print axioms BMCompactEnvelope.tendsto_supConvolution_atBot
