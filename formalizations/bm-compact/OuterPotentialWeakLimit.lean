import FilledNeighborhoodTrace
import NeighborhoodEnergyConvergence
import CapacityBoundaryAEUniqueness

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace BMCompactPDE

private theorem scalar_agrees_with_neighborhood_minimum
    {n : ℕ} {p q : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]
    (hp : 1 < p) (hpn : p < (n:ℝ)) (hq : q = (n:ℝ)*p/((n:ℝ)-p))
    {K : Set (Space n)} (hK : IsCompact K) (r : Ioi (0:ℝ))
    (u : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val K))
    (w : exteriorHomogeneousGraph p q n)
    (hw : w ∈ exteriorCapacityClass p q (BMCompact.closedNeighborhood r.val K))
    (hm : ∀ z ∈ exteriorCapacityClass p q (BMCompact.closedNeighborhood r.val K),
      ‖w.1.2‖^p ≤ ‖z.1.2‖^p) :
    u.scalar =ᵐ[volume] (w.1.1 : Space n → ℝ) := by
  subst q
  have hn1 : 1 < n := by exact_mod_cast hp.trans hpn
  have hn : 2 ≤ n := by omega
  have hcomp := BMCompact.isCompact_closedNeighborhood hK r.val
  obtain ⟨v,g,hc,hunit,hu,hg,_,hH,hbounds,hdec,hen,happ⟩ :=
    exists_continuous_unit_capacity_potential_closedNeighborhood hp hpn hK r.property
  let V : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val K) :=
    ⟨v,g,hc,hunit,hu,hH,hbounds,hdec,hen⟩
  have huv : u.scalar = v := funext fun x => le_antisymm
    (u.le_of_subset hn hcomp Subset.rfl V x) (V.le_of_subset hn hcomp Subset.rfl u x)
  have he := capacity_eq_exteriorCapacityClass_minimum_energy _ _ hp hw hm
  rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)] at he
  rw [huv]
  exact (variational_capacity_potentials_ae_unique hp hpn hcomp hu hg
    (Lp.memLp w.1.1) (Lp.memLp w.1.2) hen he happ
    (exteriorCapacityClass_smooth_approximation _ _ hw)).1

/-- An arbitrary compact set has the actual pointwise outer scalar of its
continuous capacitary neighborhood solutions. This very scalar is weakly
p-harmonic off K, with a global Lᵖ field attaining the smooth-test capacity.
Both variational components converge strongly through all positive radii. -/
theorem exists_actual_subcritical_outer_weak_potential {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hpn : p < (n:ℝ)) {K : Set (Space n)} (hK : IsCompact K) :
    ∃ U : (r : Ioi (0:ℝ)) → ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val K),
    ∃ F : Ioi (0:ℝ) → Space n → Space n, ∃ v : Space n → ℝ, ∃ g : Space n → Space n,
      (∀ x, Tendsto (fun r => (U r).scalar x) atBot (𝓝 (v x))) ∧
      UpperSemicontinuous v ∧ (∀ x ∈ fillBoundedHoles K, v x = 1) ∧
      (∀ x, 0 ≤ v x ∧ v x ≤ 1) ∧ Tendsto v (cocompact (Space n)) (𝓝 0) ∧
      WeakPHarmonicPair p Kᶜ v g ∧
      (∀ r, WeakPHarmonicPair p (BMCompact.closedNeighborhood r.val K)ᶜ (U r).scalar (F r)) ∧
      MemLp v (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume ∧ MemLp g (ENNReal.ofReal p) volume ∧
      BMCompactCapacityV2.relativeCapacity p K univ = ENNReal.ofReal (∫ x, ‖g x‖^p ∂volume) ∧
      Tendsto (fun r => eLpNorm ((U r).scalar-v) (ENNReal.ofReal ((n:ℝ)*p/((n:ℝ)-p))) volume) atBot (𝓝 0) ∧
      Tendsto (fun r => eLpNorm (F r - g) (ENNReal.ofReal p) volume) atBot (𝓝 0) := by
  classical
  let R := {r : ℝ // 0 < r}
  let _ : Nonempty R := ⟨⟨(1:ℝ),(by norm_num : (0:ℝ)<1)⟩⟩
  let q := (n:ℝ)*p/((n:ℝ)-p)
  have hpq : p ≤ q := by
    apply (le_div_iff₀ (sub_pos.mpr hpn)).mpr
    nlinarith [sq_nonneg p]
  let _ : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let _ : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr (hp.le.trans hpq)⟩
  obtain ⟨U,v,hmono,hpoint,husc,hbound,_,hdec,hv,hstrong⟩ :=
    exists_subcritical_outer_neighborhood_potential hp hpn hK
  obtain ⟨w,hw,W,hW,hm,hH,he,hlim⟩ := exists_strong_neighborhood_capacity_minimizers
    (q:=q) hp hpn rfl hK
  have hsame (r : R) := scalar_agrees_with_neighborhood_minimum hp hpn rfl hK r (U r) (W r)
    (hW r).1 (hW r).2
  let s : ℕ → R := fun j => ⟨1/((j:ℝ)+1),Nat.one_div_pos_of_nat⟩
  have hs : Antitone s := by
    intro j k hjk
    change 1/((k:ℝ)+1) ≤ 1/((j:ℝ)+1)
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.succ_le_succ hjk
  have hs0 : Tendsto s atTop atBot := by
    apply (tendsto_Ioi_atBot (a:=(0:ℝ))).mpr
    exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun j => (s j).property⟩
  have hsc : Tendsto (fun r : R => (W r).1.1) atBot (𝓝 w.1.1) :=
    (continuous_fst.comp continuous_subtype_val).continuousAt.tendsto.comp hlim
  have hgr : Tendsto (fun r : R => (W r).1.2) atBot (𝓝 w.1.2) :=
    (continuous_snd.comp continuous_subtype_val).continuousAt.tendsto.comp hlim
  have hnorm : Tendsto (fun j => eLpNorm (((W (s j)).1.1 : Space n → ℝ) -
      (hv.toLp v : Space n → ℝ)) (ENNReal.ofReal q) volume) atTop (𝓝 0) := by
    have h := hstrong s hs hs0
    apply h.congr'
    exact Eventually.of_forall fun j => eLpNorm_congr_ae
      ((hsame (s j)).sub (MemLp.coeFn_toLp hv).symm)
  have eq : w.1.1 = hv.toLp v := tendsto_nhds_unique (hsc.comp hs0)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (W (s j)).1.1) (hv.toLp v)).mpr hnorm)
  have hae : (w.1.1 : Space n → ℝ) =ᵐ[volume] v := by
    rw [eq]
    exact MemLp.coeFn_toLp hv
  have hn1 : 1 < n := by exact_mod_cast hp.trans hpn
  have hf (x : Space n) (hx : x ∈ fillBoundedHoles K) : v x = 1 := by
    have hval (r : R) := (U r).unit_on_filled (by omega) hp
      (BMCompact.isCompact_closedNeighborhood hK r.val) x
      (fillBoundedHoles_mono (BMCompact.subset_closedNeighborhood K r.val) hx)
    exact tendsto_nhds_unique (hpoint x) ((tendsto_const_nhds :
      Tendsto (fun _ : R => (1:ℝ)) atBot (𝓝 1)).congr' (Eventually.of_forall (fun r => (hval r).symm)))
  rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)] at he
  refine ⟨U,fun r => ((W r).1.2 : Space n → Space n),v,(w.1.2 : Space n → Space n),hpoint,husc,
    hf,hbound,hdec,hH.congr_ae (ae_restrict_of_ae hae) EventuallyEq.rfl,?_,hv,Lp.memLp _,he,?_,?_⟩
  · intro r
    have hh := exteriorCapacityClass_minimum_weakPHarmonic p q hp hpq
      (BMCompact.isCompact_closedNeighborhood hK r.val).isClosed (W r) (hW r).1 (hW r).2
    exact hh.congr_ae (ae_restrict_of_ae (hsame r).symm) EventuallyEq.rfl
  · apply ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun r : R => (W r).1.1) w.1.1).mp hsc).congr'
    exact Eventually.of_forall fun r => eLpNorm_congr_ae ((hsame r).symm.sub hae)
  · exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun r : R => (W r).1.2) w.1.2).mp hgr

end BMCompactPDE
#print axioms BMCompactPDE.exists_actual_subcritical_outer_weak_potential
