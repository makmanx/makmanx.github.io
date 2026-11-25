import JLMComparison
import NonlinearEnvelope
import SubcriticalCapacityComparison
import OuterPointwiseComparison
import CriticalCapacityReduction
import CriticalOuterGreenLimit
import SupercriticalTheoremA
import UnitPotentialSigns
import GreenFilling
import SupConvolutionGreenTail

/-!
General Proposition 7.3 (nonlinear comparison for the sup-min envelope) and the
full unconditional Theorems A(a), A(c), B(c), C(a), C(b), and C(c) of
`BM_Compact_Final.tex` for all `1 < p < ∞` and all dimensions `n ≥ 2`.
-/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Bornology BMCompactEnvelope BMCompactAnalytic BMCompactCapacityV2
open scoped Topology Pointwise ENNReal
namespace BMCompactPDE

section Prop73Subcritical

private theorem unit_strict_harmonic_allp {n : ℕ} {p : ℝ} {K : Set (Space n)}
    (u : ContinuousUnitCapacityData p K) :
    WeakPHarmonicPair p {x | u.scalar x < 1} u.scalar u.field := by
  apply u.harmonic.mono _ (isOpen_lt u.continuous_scalar continuous_const)
  intro x hx hxK
  exact hx.ne (u.unit x hxK)

/-- **Proposition 7.3 (subcritical envelope comparison)** for all `1 < p < ∞` and `n ≥ 2`:
the supremal convolution of two independent continuous unit `p`-potentials is
bounded above by the continuous unit `p`-potential of the weighted Minkowski sum. -/
theorem ContinuousUnitCapacityData.envelope_le_allp {n : ℕ} {p : ℝ}
    (hn : 2 ≤ n) (hp : 1 < p)
    {K L : Set (Space n)} (hK : IsCompact K) (hL : IsCompact L)
    (hne : K.Nonempty) (hne' : L.Nonempty)
    (u : ContinuousUnitCapacityData p K) (v : ContinuousUnitCapacityData p L)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (w : ContinuousUnitCapacityData p (t • K + (1 - t) • L)) (x : Space n) :
    supConvolution t u.scalar v.scalar x ≤ w.scalar x := by
  let S := t • K + (1 - t) • L
  let W := supConvolution t u.scalar v.scalar
  have hS : IsCompact S := (hK.smul t).add (hL.smul (1 - t))
  have htne := (sub_pos.mpr ht1).ne'
  have hu0 := u.pos_of_nonempty hn hK hne
  have hv0 := v.pos_of_nonempty hn hL hne'
  have hut : Tendsto u.scalar (cobounded (Space n)) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using u.decay
  have hvt : Tendsto v.scalar (cobounded (Space n)) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using v.decay
  have hu1 := fun y => (u.bounds y).2
  have hWc : Continuous W := continuous_supConvolution_subcritical t htne u.continuous_scalar
    v.continuous_scalar hu0 hv0 hut
  have hW1 (a : Space n) : W a ≤ 1 := (supConvolution_bounds t (v := v.scalar) hu1 a).2
  have hWt : Tendsto W (cocompact (Space n)) (𝓝 0) := by
    simpa only [Metric.cobounded_eq_cocompact] using tendsto_supConvolution_zero t htne
      u.continuous_scalar v.continuous_scalar hu0 hv0 hut hvt hu1
  have htop (a : Space n) (ha : W a = 1) : w.scalar a = 1 := by
    obtain ⟨y, z, hyz, hm⟩ := exists_optimalPair_subcritical t htne u.continuous_scalar
      v.continuous_scalar hu0 hv0 hut a
    have hm1 : 1 ≤ min (u.scalar y) (v.scalar z) := ha.ge.trans hm.le
    have hy := (u.eq_one_iff_mem_fill hn hp hK y).mp (le_antisymm (hu1 y) (le_min_iff.mp hm1).1)
    have hz := (v.eq_one_iff_mem_fill hn hp hL z).mp (le_antisymm (v.bounds z).2 (le_min_iff.mp hm1).2)
    apply w.unit_on_filled hn hp hS a
    apply smul_fill_add_smul_fill_subset hn hK hL hne hne' ht ht1
    exact ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, hz, rfl⟩, hyz.symm⟩
  let Ω : Set (Space n) := {a | W a < 1} ∩ Sᶜ
  have hΩ : IsOpen Ω := (isOpen_lt hWc continuous_const).inter hS.isClosed.isOpen_compl
  have hWvisc : IsViscosityPSubsolution p {a | W a < 1} W :=
    weak_viscosity_supConvolution_subcritical_allp hn hp ht ht1 u.continuous_scalar
      v.continuous_scalar hu0 hv0 hut hu1
      ⟨_, unit_strict_harmonic_allp u⟩ ⟨_, unit_strict_harmonic_allp v⟩
  have hvis := hWvisc.mono hΩ inter_subset_left
  have hwh := w.harmonic.mono (show Ω ⊆ Sᶜ from inter_subset_right) hΩ
  have hdiff : Tendsto (fun a => W a - w.scalar a) (cocompact (Space n)) (𝓝 0) := by
    simpa using hWt.sub w.decay
  by_contra! hbad
  let ε := (W x - w.scalar x) / 2
  have hε : 0 < ε := half_pos (sub_pos.mpr hbad)
  let E : Set (Space n) := {a | ε ≤ W a - w.scalar a}
  obtain ⟨T, hT, hET⟩ := mem_cocompact'.mp (hdiff.eventually_lt_const hε)
  have hE : IsCompact E := hT.of_isClosed_subset
    (isClosed_le continuous_const (hWc.sub w.continuous_scalar))
    (fun a (ha : ε ≤ W a - w.scalar a) => hET (not_lt.mpr ha))
  have hEΩ : E ⊆ Ω := by
    intro a ha
    change ε ≤ W a - w.scalar a at ha
    have hw1 : w.scalar a < 1 := by linarith only [hW1 a, hε, ha]
    exact ⟨lt_of_le_of_ne (hW1 a) (fun he => hw1.ne (htop a he)), fun haS => hw1.ne (w.unit a haS)⟩
  obtain ⟨r, hr, hrΩ⟩ := hE.exists_cthickening_subset_open hΩ hEΩ
  let D := thickening r E
  have hD : LocalDomain D Ω := ⟨isOpen_thickening, hE.isBounded.thickening,
    (closure_thickening_subset_cthickening r E).trans hrΩ⟩
  have hED := self_subset_thickening hr E
  have hb (a : Space n) (ha : a ∈ frontier D) : W a ≤ w.scalar a + ε := by
    have hnD : a ∉ D := (hD.1.frontier_eq ▸ ha).2
    have hnE : a ∉ E := fun h => hnD (hED h)
    have hlt : W a - w.scalar a < ε := lt_of_not_ge hnE
    linarith only [hlt]
  have hxE : x ∈ E := by
    change (W x - w.scalar x) / 2 ≤ W x - w.scalar x
    linarith only [hε, show 0 < W x - w.scalar x from sub_pos.mpr hbad]
  have hcmp := (hwh.add_const ε).viscosity_le_allp
    (w.continuous_scalar.add continuous_const).continuousOn
    hvis hWc.continuousOn hn hD hb x (hED hxE)
  change W x ≤ w.scalar x + (W x - w.scalar x) / 2 at hcmp
  change w.scalar x < W x at hbad
  linarith only [hcmp, hbad]

/-- **Theorem C(a) (subcritical / unit-potential half)** for all `1 < p < ∞` and `n ≥ 2`:
pointwise minimum comparison for three continuous unit `p`-potentials. -/
theorem ContinuousUnitCapacityData.min_le_allp {n : ℕ} {p : ℝ}
    (hn : 2 ≤ n) (hp : 1 < p)
    {K L : Set (Space n)} (hK : IsCompact K) (hL : IsCompact L)
    (hne : K.Nonempty) (hne' : L.Nonempty)
    (u : ContinuousUnitCapacityData p K) (v : ContinuousUnitCapacityData p L)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (w : ContinuousUnitCapacityData p (t • K + (1 - t) • L)) (y z : Space n) :
    min (u.scalar y) (v.scalar z) ≤ w.scalar (t • y + (1 - t) • z) :=
  (min_le_supConvolution_of_decomposition t (v := v.scalar) (fun a => (u.bounds a).2) rfl).trans
    (u.envelope_le_allp hn hp hK hL hne hne' v ht ht1 w _)

end Prop73Subcritical

section Prop73Green

private theorem neg_green_strict_harmonic_allp {n : ℕ} {p σ : ℝ} {K : Set (Space n)}
    {G : Space n → ℝ} (hG : IsExteriorGreen n σ p K G) :
    IsWeakPHarmonic p {y | -G y < 0} (fun y => -G y) := by
  obtain ⟨_, _, _, _, _, hc, h0, ⟨g, hg⟩, _⟩ := hG
  have hopen : IsOpen {y | -G y < 0} := isOpen_lt hc.neg continuous_const
  have hsub : {y | -G y < 0} ⊆ Kᶜ := by
    intro y hy hyK
    change -G y < 0 at hy
    simp only [h0 hyK, neg_zero, lt_self_iff_false] at hy
  exact ⟨(-1 : ℝ) • g, by simpa only [neg_one_smul, Pi.neg_def] using (hg.mono hsub hopen).smul (-1)⟩

/-- **Proposition 7.3 & Theorem C(a) (critical and supercritical Green half)**
for all `n ≥ 2` and all `p ≥ n`: pointwise maximum comparison for three
normalized exterior `p`-Green functions. -/
theorem IsExteriorGreen.green_max_comparison_allp {n : ℕ} {p σ t : ℝ}
    (hn : 2 ≤ n) {K L : Set (Space n)} {u v w : Space n → ℝ}
    (hu : IsExteriorGreen n σ p K u) (hv : IsExteriorGreen n σ p L v)
    (ht : 0 < t) (ht1 : t < 1) (hw : IsExteriorGreen n σ p (t • K + (1 - t) • L) w)
    (y z : Space n) :
    w (t • y + (1 - t) • z) ≤ max (u y) (v z) := by
  let S := t • K + (1 - t) • L
  let U := fun a => -u a
  let V := fun a => -v a
  let W := supConvolution t U V
  have huc : Continuous U := hu.2.2.2.2.2.1.neg
  have hvc : Continuous V := hv.2.2.2.2.2.1.neg
  have hwc := hw.2.2.2.2.2.1
  have htne := (sub_pos.mpr ht1).ne'
  have hp : 1 < p := by
    have h2 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    exact lt_of_lt_of_le h2 hu.2.1
  have htU : Tendsto U (cobounded _) atBot := tendsto_neg_atTop_atBot.comp hu.tendsto_atTop_at_infinity
  have hWc : Continuous W := continuous_supConvolution_atBot t htne huc hvc htU
  have hU0 (a : Space n) : U a ≤ 0 := neg_nonpos.mpr (hu.nonnegative a)
  have hW0 (a : Space n) : W a ≤ 0 := (supConvolution_bounds t (v := V) hU0 a).2
  have hVsub : IsViscosityPSubsolution p {x | W x < 0} W :=
    weak_viscosity_supConvolution_atBot_allp hn hp ht ht1 huc hvc htU hU0
      (neg_green_strict_harmonic_allp hu) (neg_green_strict_harmonic_allp hv)
  have htop (a : Space n) (ha : W a = 0) : w a = 0 := by
    obtain ⟨b, d, hbd, hm⟩ := exists_optimalPair_atBot t htne huc hvc htU a
    have hl : 0 ≤ min (U b) (V d) := ha.ge.trans hm.le
    have hBu : b ∈ fillBoundedHoles K := by
      rw [hu.fill_eq_zero_set]; change u b = 0
      exact le_antisymm (neg_nonneg.mp (le_min_iff.mp hl).1) (hu.nonnegative b)
    have hDv : d ∈ fillBoundedHoles L := by
      rw [hv.fill_eq_zero_set]; change v d = 0
      exact le_antisymm (neg_nonneg.mp (le_min_iff.mp hl).2) (hv.nonnegative d)
    have hwf := smul_fill_add_smul_fill_subset hn hu.2.2.2.1 hv.2.2.2.1
      hu.2.2.2.2.1 hv.2.2.2.2.1 ht ht1 (a := a) ⟨_, ⟨b, hBu, rfl⟩, _, ⟨d, hDv, rfl⟩, hbd.symm⟩
    simpa only [hw.fill_eq_zero_set, mem_ofPred_eq] using hwf
  let Ω : Set (Space n) := {a | W a < 0} ∩ Sᶜ
  have hS : IsCompact S := hw.2.2.2.1
  have hΩ : IsOpen Ω := (isOpen_lt hWc continuous_const).inter hS.isClosed.isOpen_compl
  obtain ⟨g, hg⟩ := hw.2.2.2.2.2.2.2.1
  have hh := hg.mono (show Ω ⊆ Sᶜ from inter_subset_right) hΩ
  have hcmp (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x : Space n) : W x ≤ -θ * w x + (1 - θ) := by
    let ε := 1 - θ
    have hε : 0 < ε := sub_pos.mpr hθ1
    let E : Set (Space n) := {a | ε ≤ W a + θ * w a}
    have hinf : Tendsto (fun a => W a + θ * w a) (cocompact _) atBot := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_negativeGreenEnvelope_add_atBot n hu.1 hu.2.1 hu.2.2.1 ht.le ht1.le hθ hθ1
        hu.2.2.2.2.2.2.2.2 hv.2.2.2.2.2.2.2.2 hw.2.2.2.2.2.2.2.2
    obtain ⟨T, hT, hET⟩ := mem_cocompact'.mp (hinf.eventually (eventually_lt_atBot ε))
    have hE : IsCompact E := hT.of_isClosed_subset
      (isClosed_le continuous_const (hWc.add (hwc.const_mul θ)))
      (fun a (ha : ε ≤ W a + θ * w a) => hET (not_lt.mpr ha))
    have hEΩ : E ⊆ Ω := by
      intro a ha
      change ε ≤ W a + θ * w a at ha
      have hwne : w a ≠ 0 := by intro hz; rw [hz, mul_zero, add_zero] at ha; linarith only [hW0 a, hε, ha]
      exact ⟨lt_of_le_of_ne (hW0 a) (fun h => hwne (htop a h)), fun h => hwne (hw.2.2.2.2.2.2.1 h)⟩
    obtain ⟨r, hr, hrΩ⟩ := hE.exists_cthickening_subset_open hΩ hEΩ
    let D := thickening r E
    have hD : LocalDomain D Ω := ⟨isOpen_thickening, hE.isBounded.thickening,
      (closure_thickening_subset_cthickening r E).trans hrΩ⟩
    have hED := self_subset_thickening hr E
    have hb (a : Space n) (ha : a ∈ frontier D) : W a ≤ -θ * w a + ε := by
      have hnD : a ∉ D := (hD.1.frontier_eq ▸ ha).2
      have hnE : a ∉ E := fun h => hnD (hED h)
      have hlt : W a + θ * w a < ε := lt_of_not_ge hnE
      linarith only [hlt]
    have hlocal := ((hh.smul (-θ)).add_const ε).viscosity_le_allp
      ((hwc.const_smul (-θ)).add continuous_const).continuousOn
      (hVsub.mono hΩ inter_subset_left) hWc.continuousOn hn hD
      (fun a ha => by simpa [Pi.smul_apply, smul_eq_mul] using hb a ha)
    by_contra! hbad
    have hxE : x ∈ E := by
      change ε ≤ W x + θ * w x
      change -θ * w x + ε < W x at hbad
      linarith only [hbad]
    exact hbad.not_ge (by simpa [Pi.smul_apply, smul_eq_mul] using hlocal x (hED hxE))
  let a := t • y + (1 - t) • z
  have hf : Tendsto (fun θ : ℝ => -θ * w a + (1 - θ)) (𝓝[<] 1) (𝓝 (-w a)) := by
    have hc : Continuous (fun θ : ℝ => -θ * w a + (1 - θ)) := by fun_prop
    simpa using hc.continuousAt.continuousWithinAt.tendsto (s := Iio (1 : ℝ)) (x := (1 : ℝ))
  have hWa : W a ≤ -w a := by
    apply ge_of_tendsto hf
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with θ hθ hθ0
    exact hcmp θ hθ0.le hθ a
  have hl := (min_le_supConvolution_of_decomposition t (v := V) hU0 (show a = t • y + (1 - t) • z from rfl)).trans hWa
  change min (-(u y)) (-(v z)) ≤ -(w a) at hl
  exact neg_le_neg_iff.mp (by simpa only [min_neg_neg] using hl)

end Prop73Green

section GeneralTheorems

private theorem cast_scalar {n : ℕ} {p : ℝ} {K₁ K₂ : Set (Space n)} (h : K₁ = K₂)
    (w : ContinuousUnitCapacityData p K₁) (x : Space n) :
    (h ▸ w).scalar x = w.scalar x := by
  subst h; rfl

/-- **General Theorem A(a)** for ALL `1 < p < n` and ALL nonempty compact pairs `E, F ⊂ ℝⁿ`. -/
theorem theoremA_subcritical_allp {n : ℕ} {p : ℝ} (hp : 1 < p) (hpn : p < (n : ℝ))
    {E F : Set (Space n)} (hE : IsCompact E) (hF : IsCompact F)
    (he : E.Nonempty) (hf : F.Nonempty) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal t * variationalCapacity p E ^ (1 / ((n : ℝ) - p)) +
      ENNReal.ofReal (1 - t) * variationalCapacity p F ^ (1 / ((n : ℝ) - p)) ≤
        variationalCapacity p (t • E + (1 - t) • F) ^ (1 / ((n : ℝ) - p)) := by
  have hn : 2 ≤ n := by
    have h1 : (1 : ℝ) < (n : ℝ) := hp.trans hpn
    have h1' : 1 < n := by exact_mod_cast h1
    omega
  apply theoremA_subcritical_of_diagonal_comparison hp hpn _ hE hF he hf ht ht1
  intro K L hK hL hk hl s hs hs1 δ hδ u v w x
  have hgeom : s • BMCompact.closedNeighborhood δ K + (1 - s) • BMCompact.closedNeighborhood δ L =
      BMCompact.closedNeighborhood δ (s • K + (1 - s) • L) :=
    BMCompact.weighted_closedNeighborhood hK hL hs.le hs1.le hδ.le
  let hw' : ContinuousUnitCapacityData p
      (s • BMCompact.closedNeighborhood δ K + (1 - s) • BMCompact.closedNeighborhood δ L) :=
    hgeom.symm ▸ w
  have hcmp := u.min_le_allp hn hp
    (BMCompact.isCompact_closedNeighborhood hK δ) (BMCompact.isCompact_closedNeighborhood hL δ)
    (hk.mono (BMCompact.subset_closedNeighborhood K δ)) (hl.mono (BMCompact.subset_closedNeighborhood L δ))
    v hs hs1 hw' x x
  have hxx : s • x + (1 - s) • x = x := by rw [← add_smul, add_sub_cancel, one_smul]
  rw [hxx] at hcmp
  simpa only [hw', cast_scalar] using hcmp

/-- **General Theorem C(b)** for ALL `1 < p < n` and ALL nonempty compact pairs `E, F ⊂ ℝⁿ`,
including both the pointwise and lower semicontinuous regularization inequalities. -/
theorem theoremC_subcritical_outer_allp {n : ℕ} {p : ℝ} (hp : 1 < p) (hpn : p < (n : ℝ))
    {E F : Set (Space n)} (hE : IsCompact E) (hF : IsCompact F)
    (hne : E.Nonempty) (hne' : F.Nonempty) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ U : (r : Ioi (0 : ℝ)) → ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val E),
    ∃ V : (r : Ioi (0 : ℝ)) → ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val F),
    ∃ W : (r : Ioi (0 : ℝ)) → ContinuousUnitCapacityData p
      (BMCompact.closedNeighborhood r.val (t • E + (1 - t) • F)),
    ∃ u v w : Space n → ℝ,
      (∀ x, Tendsto (fun r => (U r).scalar x) atBot (𝓝 (u x))) ∧
      (∀ x, Tendsto (fun r => (V r).scalar x) atBot (𝓝 (v x))) ∧
      (∀ x, Tendsto (fun r => (W r).scalar x) atBot (𝓝 (w x))) ∧
      (∀ y z, min (u y) (v z) ≤ w (t • y + (1 - t) • z)) ∧
      ∀ y z, min (liminf u (𝓝 y)) (liminf v (𝓝 z)) ≤
        liminf w (𝓝 (t • y + (1 - t) • z)) := by
  have hn : 2 ≤ n := by
    have h1 : (1 : ℝ) < (n : ℝ) := hp.trans hpn
    have h1' : 1 < n := by exact_mod_cast h1
    omega
  apply theoremC_subcritical_outer_of_neighborhood_comparison hp hpn hE hF ht.le ht1.le
  intro r U V W y z
  exact U.min_le_allp hn hp
    (BMCompact.isCompact_closedNeighborhood hE r.val)
    (BMCompact.isCompact_closedNeighborhood hF r.val)
    (hne.mono (BMCompact.subset_closedNeighborhood E r.val))
    (hne'.mono (BMCompact.subset_closedNeighborhood F r.val))
    V ht ht1 W y z

/-- **General Theorem B(c)** for ALL critical dimensions `p = n ≥ 2` and ALL nonempty
compact pairs `E, F ⊂ ℝⁿ`. -/
theorem theoremB_critical_allp {n : ℕ} (hn : 2 ≤ n)
    {E F : Set (Space n)} (hE : IsCompact E) (hF : IsCompact F)
    (he : E.Nonempty) (hf : F.Nonempty) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * canonicalCriticalOuterCapacity E +
      (1 - t) * canonicalCriticalOuterCapacity F ≤
        canonicalCriticalOuterCapacity (t • E + (1 - t) • F) := by
  apply theoremB_critical_of_neighborhood_comparison hn _ hE hF he hf ht ht1
  intro K L hK hL _ _ s hs hs1 δ hδ G H J hG hH hJ y z
  have hgeom : s • BMCompact.closedNeighborhood δ K + (1 - s) • BMCompact.closedNeighborhood δ L =
      BMCompact.closedNeighborhood δ (s • K + (1 - s) • L) :=
    BMCompact.weighted_closedNeighborhood hK hL hs.le hs1.le hδ.le
  exact hG.green_max_comparison_allp hn hH hs hs1 (hgeom.symm ▸ hJ) y z

/-- **General Theorem C(c)** for ALL critical dimensions `p = n ≥ 2` and ALL nonempty
compact pairs `E, F ⊂ ℝⁿ`. -/
theorem theoremC_critical_outer_allp {n : ℕ} (hn : 2 ≤ n)
    {E F : Set (Space n)} (hE : IsCompact E) (he : E.Nonempty)
    (hF : IsCompact F) (hf : F.Nonempty) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ U V W : Ioi (0 : ℝ) → Space n → ℝ, ∃ u v w : Space n → ℝ≥0∞,
      (∀ r, IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood r.val E) (U r) ∧
        IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood r.val F) (V r) ∧
        IsExteriorGreen n (canonicalSphereArea n) n
          (BMCompact.closedNeighborhood r.val (t • E + (1 - t) • F)) (W r)) ∧
      (∀ x, Tendsto (fun r => ENNReal.ofReal (U r x)) atBot (𝓝 (u x)) ∧
        Tendsto (fun r => ENNReal.ofReal (V r x)) atBot (𝓝 (v x)) ∧
        Tendsto (fun r => ENNReal.ofReal (W r x)) atBot (𝓝 (w x))) ∧
      ∀ y z, w (t • y + (1 - t) • z) ≤ max (u y) (v z) := by
  apply theoremC_critical_outer_of_neighborhood_comparison hn ht.le ht1.le hE he hF hf
  intro r U V W hU hV hW y z
  exact hU.green_max_comparison_allp hn hV ht ht1 hW y z

/-- **General Theorem A(c)** for ALL supercritical `p > n ≥ 2` and ALL nonempty
compact pairs `E, F ⊂ ℝⁿ`. -/
theorem theoremA_supercritical_allp {n : ℕ} {p : ℝ} (hn : 2 ≤ n) (hnp : (n : ℝ) < p)
    {E F : Set (Space n)} (hE : IsCompact E) (hF : IsCompact F)
    (he : E.Nonempty) (hf : F.Nonempty) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * canonicalSupercriticalGreenCapacity p E ^ (1 / (p - (n : ℝ))) +
      (1 - t) * canonicalSupercriticalGreenCapacity p F ^ (1 / (p - (n : ℝ))) ≤
        canonicalSupercriticalGreenCapacity p (t • E + (1 - t) • F) ^ (1 / (p - (n : ℝ))) := by
  have hp1 : 1 < p := lt_trans (by exact_mod_cast (show 1 < n by omega)) hnp
  have hpn_pos : 0 < p - (n : ℝ) := sub_pos.mpr hnp
  have hexp_pos : 0 < 1 / (p - (n : ℝ)) := one_div_pos.mpr hpn_pos
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [zero_smul_set he]
  rcases eq_or_lt_of_le ht1 with rfl | ht1
  · simp [zero_smul_set hf]
  -- Helper: min-comparison for supercritical capacity from green_max_comparison_allp
  have hmin : ∀ {K L : Set (Space n)}, IsCompact K → IsCompact L → K.Nonempty → L.Nonempty →
      ∀ {s : ℝ}, 0 < s → s < 1 →
        min (canonicalSupercriticalGreenCapacity p K) (canonicalSupercriticalGreenCapacity p L) ≤
          canonicalSupercriticalGreenCapacity p (s • K + (1 - s) • L) := by
    intro K L hK hL hk hl s hs hs1
    obtain ⟨G, k, hG, hk', heK⟩ := has_canonical_supercritical_green_capacity hn hnp hK hk
    obtain ⟨H, l, hH, hl', heL⟩ := has_canonical_supercritical_green_capacity hn hnp hL hl
    obtain ⟨J, m, hJ, hm', heM⟩ := has_canonical_supercritical_green_capacity hn hnp
      ((hK.smul s).add (hL.smul (1 - s))) ((hk.image _).add (hl.image _))
    have hcmp := hG.green_max_comparison_allp hn hH hs hs1 hJ
    have : NeZero n := ⟨by omega⟩
    have : Nontrivial (Space n) := inferInstance
    have hkl : m ≤ max k l := le_of_tendsto_of_tendsto' hm' (hk'.max hl') fun x => by
      change J x - fundamentalPotential n _ _ x ≤ max (G x - _) (H x - _)
      rw [max_sub_sub_right]
      apply sub_le_sub_right
      have heq : s • x + (1 - s) • x = x := by rw [← add_smul, add_sub_cancel, one_smul]
      simpa only [heq] using hcmp x x
    rw [heK, heL, heM]
    simp only [greenCapacityOfConstant, if_neg hnp.ne']
    rcases le_total k l with h | h
    · rw [max_eq_right h] at hkl
      exact (min_le_right _ _).trans (Real.rpow_le_rpow
        (neg_nonneg.mpr (hH.supercritical_constant_nonpos hnp hl'))
        (neg_le_neg hkl) (sub_pos.mpr hp1).le)
    · rw [max_eq_left h] at hkl
      exact (min_le_left _ _).trans (Real.rpow_le_rpow
        (neg_nonneg.mpr (hG.supercritical_constant_nonpos hnp hk'))
        (neg_le_neg hkl) (sub_pos.mpr hp1).le)
  -- Helper: dilation of cap^(1/(p-n))
  have hdil {K : Set (Space n)} (hK : IsCompact K) (hk : K.Nonempty) {s : ℝ} (hs : 0 < s) :
      canonicalSupercriticalGreenCapacity p (s • K) ^ (1 / (p - (n : ℝ))) =
        s * canonicalSupercriticalGreenCapacity p K ^ (1 / (p - (n : ℝ))) := by
    have h0 : s • K = s • K + {(0 : Space n)} := by simp
    rw [h0, canonicalSupercriticalGreenCapacity_similarity hn hnp hK hk hs 0,
      Real.mul_rpow (Real.rpow_nonneg hs.le _) (canonicalSupercriticalGreenCapacity_nonneg hn hnp hK hk),
      ← Real.rpow_mul hs.le, show (p - (n : ℝ)) * (1 / (p - (n : ℝ))) = 1 by field_simp [hpn_pos.ne'],
      Real.rpow_one]
  -- Helper: weighted lower bound t * cap(K)^(1/(p-n)) ≤ cap(t•K + (1-t)•L)^(1/(p-n))
  have hleft {K L : Set (Space n)} (hK : IsCompact K) (hL : IsCompact L)
      (hk : K.Nonempty) (hl : L.Nonempty) {s : ℝ} (hs : 0 < s) :
      s * canonicalSupercriticalGreenCapacity p K ^ (1 / (p - (n : ℝ))) ≤
        canonicalSupercriticalGreenCapacity p (s • K + (1 - s) • L) ^ (1 / (p - (n : ℝ))) := by
    obtain ⟨y, hy⟩ := hl
    have hsub : s • K + {(1 - s) • y} ⊆ s • K + (1 - s) • L := by
      rintro _ ⟨z, hz, w, hw, rfl⟩
      obtain rfl : w = (1 - s) • y := hw
      exact ⟨z, hz, _, ⟨y, hy, rfl⟩, rfl⟩
    have hmono := canonicalSupercriticalGreenCapacity_mono hn hnp
      ((hK.smul s).add isCompact_singleton) ((hK.smul s).add (hL.smul (1 - s)))
      ((hk.image _).add (singleton_nonempty _)) hsub
    have hrp := Real.rpow_le_rpow
      (canonicalSupercriticalGreenCapacity_nonneg hn hnp ((hK.smul s).add isCompact_singleton)
        ((hk.image _).add (singleton_nonempty _))) hmono hexp_pos.le
    rw [canonicalSupercriticalGreenCapacity_similarity hn hnp hK hk hs ((1 - s) • y),
      Real.mul_rpow (Real.rpow_nonneg hs.le _) (canonicalSupercriticalGreenCapacity_nonneg hn hnp hK hk),
      ← Real.rpow_mul hs.le, show (p - (n : ℝ)) * (1 / (p - (n : ℝ))) = 1 by field_simp [hpn_pos.ne'],
      Real.rpow_one] at hrp
    exact hrp
  let a := canonicalSupercriticalGreenCapacity p E ^ (1 / (p - (n : ℝ)))
  let b := canonicalSupercriticalGreenCapacity p F ^ (1 / (p - (n : ℝ)))
  have ha_nn : 0 ≤ a := Real.rpow_nonneg (canonicalSupercriticalGreenCapacity_nonneg hn hnp hE he) _
  have hb_nn : 0 ≤ b := Real.rpow_nonneg (canonicalSupercriticalGreenCapacity_nonneg hn hnp hF hf) _
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · let A := BMCompact.normalizationScale t a b
      let s := BMCompact.normalizationWeight t a b
      have hA := BMCompact.normalizationScale_pos ht ht1 ha hb
      have hsl := BMCompact.normalizationWeight_pos ht ht1 ha hb
      have hsr := BMCompact.normalizationWeight_lt_one ht ht1 ha hb
      have hm := hmin (hE.smul a⁻¹) (hF.smul b⁻¹) (he.image _) (hf.image _) hsl hsr
      have hm_rpow := Real.rpow_le_rpow
        (le_min (canonicalSupercriticalGreenCapacity_nonneg hn hnp (hE.smul a⁻¹) (he.image _))
          (canonicalSupercriticalGreenCapacity_nonneg hn hnp (hF.smul b⁻¹) (hf.image _)))
        hm hexp_pos.le
      have hmin_rpow : min (canonicalSupercriticalGreenCapacity p (a⁻¹ • E) ^ (1 / (p - (n : ℝ))))
          (canonicalSupercriticalGreenCapacity p (b⁻¹ • F) ^ (1 / (p - (n : ℝ)))) ≤
          canonicalSupercriticalGreenCapacity p (s • (a⁻¹ • E) + (1 - s) • (b⁻¹ • F)) ^ (1 / (p - (n : ℝ))) := by
        rcases le_total (canonicalSupercriticalGreenCapacity p (a⁻¹ • E))
            (canonicalSupercriticalGreenCapacity p (b⁻¹ • F)) with h | h
        · rw [min_eq_left h] at hm_rpow; exact (min_le_left _ _).trans hm_rpow
        · rw [min_eq_right h] at hm_rpow; exact (min_le_right _ _).trans hm_rpow
      rw [hdil hE he (inv_pos.mpr ha), hdil hF hf (inv_pos.mpr hb)] at hmin_rpow
      change min (a⁻¹ * a) (b⁻¹ * b) ≤ _ at hmin_rpow
      rw [inv_mul_cancel₀ ha.ne', inv_mul_cancel₀ hb.ne', min_self,
        BMCompactCapacityV2.normalization_pointwise_set_identity ht ht1 ha hb E F,
        hdil ((hE.smul t).add (hF.smul (1 - t))) ((he.image _).add (hf.image _)) (inv_pos.mpr hA)] at hmin_rpow
      have hh := mul_le_mul_of_nonneg_left hmin_rpow hA.le
      rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at hh
      exact hh
    · have hz : canonicalSupercriticalGreenCapacity p F ^ (1 / (p - (n : ℝ))) = 0 :=
        le_antisymm (le_of_not_gt hb) hb_nn
      rw [hz, mul_zero, add_zero]
      exact hleft hE hF he hf ht
  · have hz : canonicalSupercriticalGreenCapacity p E ^ (1 / (p - (n : ℝ))) = 0 :=
      le_antisymm (le_of_not_gt ha) ha_nn
    have hcomm : t • E + (1 - t) • F = (1 - t) • F + (1 - (1 - t)) • E := by
      rw [sub_sub_cancel, add_comm]
    rw [hcomm, hz, mul_zero, zero_add]
    exact hleft hF hE hf he (sub_pos.mpr ht1)

end GeneralTheorems
end BMCompactPDE
#print axioms BMCompactPDE.ContinuousUnitCapacityData.envelope_le_allp
#print axioms BMCompactPDE.ContinuousUnitCapacityData.min_le_allp
#print axioms BMCompactPDE.IsExteriorGreen.green_max_comparison_allp
#print axioms BMCompactPDE.theoremA_subcritical_allp
#print axioms BMCompactPDE.theoremA_supercritical_allp
#print axioms BMCompactPDE.theoremB_critical_allp
#print axioms BMCompactPDE.theoremC_subcritical_outer_allp
#print axioms BMCompactPDE.theoremC_critical_outer_allp
