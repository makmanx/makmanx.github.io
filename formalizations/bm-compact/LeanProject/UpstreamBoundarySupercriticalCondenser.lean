import UpstreamBoundaryMorreyConvergence
import UpstreamBoundaryRelativeClamp
import ExteriorCondenserConstruction

/-! Genuine continuous unit-trace relative capacitary potentials above the
dimension, for arbitrary compact obstacles including thin sets. Actual W0 zero
extension and actual strong admissible approximants feed Morrey convergence at
EVERY point. Neither pointwise trace nor boundary regularity is a premise. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem upstream_continuous_global_unit_bounds {n : ℕ} {u : Space n → ℝ}
    (hu : Continuous u) (hb : ∀ᵐ x ∂volume,0≤u x ∧ u x≤1) :
    ∀ x,0≤u x ∧ u x≤1 := by
  have hlow : (fun x=>max (-u x) 0)=ᵐ[volume.restrict univ] (fun _=>0) := by
    filter_upwards [ae_restrict_of_ae hb] with x hx
    exact max_eq_right (neg_nonpos.mpr hx.1)
  have hupp : (fun x=>max (u x-1) 0)=ᵐ[volume.restrict univ] (fun _=>0) := by
    filter_upwards [ae_restrict_of_ae hb] with x hx
    exact max_eq_right (sub_nonpos.mpr hx.2)
  have hl := Measure.eqOn_open_of_ae_eq hlow isOpen_univ
    ((show Continuous (fun t : ℝ=>max (-t) 0) by fun_prop).comp hu).continuousOn continuousOn_const
  have hh := Measure.eqOn_open_of_ae_eq hupp isOpen_univ
    ((show Continuous (fun t : ℝ=>max (t-1) 0) by fun_prop).comp hu).continuousOn continuousOn_const
  intro x
  exact ⟨neg_nonpos.mp ((le_max_left (-u x) 0).trans_eq (hl (mem_univ x))),
    sub_nonpos.mp ((le_max_left (u x-1) 0).trans_eq (hh (mem_univ x)))⟩

set_option maxHeartbeats 1000000 in
theorem exists_continuous_unit_relative_capacity_potential_supercritical
    {n : ℕ} {p : ℝ} (hn : 2≤n) (hnp : (n:ℝ)<p) {K O : Set (Space n)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O) (hOb : Bornology.IsBounded O) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      Continuous u ∧ (∀ x∈K,u x=1) ∧ (∀ x∉O,u x=0) ∧ (∀ x,0≤u x ∧ u x≤1) ∧
      ZeroBoundarySobolevPair p O u g ∧ SobolevPair p univ u g ∧
      WeakPHarmonicPair p (O\K) u g ∧
      BMCompactCapacityV2.relativeCapacity p K O=ENNReal.ofReal (∫ x in O,‖g x‖^p ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K O (φ j)) ∧
        Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
        Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  classical
  have hn1 : 1≤n := (by norm_num : 1≤(2:ℕ)).trans hn
  have hp : 1<p := (by exact_mod_cast hn1 : (1:ℝ)≤(n:ℝ)).trans_lt hnp
  obtain ⟨u,g,hu,hH,hunit,hcap,φ,hφ,hlu,hlg⟩ :=
    exists_bounded_relative_capacity_potential_unit_bounds_allp hp hn hK hO hKO hOb
  let U : Space n → ℝ := O.indicator u
  let G : Space n → Space n := O.indicator g
  have hExt : ZeroBoundarySobolevPair p univ U G := hu.zeroExtend_to_superset hO.measurableSet (subset_univ O)
  have hφ0 (j : ℕ) (x : Space n) (hx : x∉O) : φ j x=0 :=
    image_eq_zero_of_notMem_tsupport (fun ht=>hx ((hφ j).2.2.1 ht))
  have hgφ0 (j : ℕ) (x : Space n) (hx : x∉O) : gradient (φ j) x=0 :=
    BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport (fun ht=>hx ((hφ j).2.2.1 ht))
  have hluG : Tendsto (fun j=>eLpNorm (φ j-U) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    have heq (j : ℕ) : φ j-U=O.indicator (φ j-u) := by
      funext x
      by_cases hx : x∈O
      · simp only [U,Pi.sub_apply,indicator_of_mem hx]
      · simp only [U,Pi.sub_apply,indicator_of_notMem hx,hφ0 j x hx,sub_zero]
    simp_rw [heq,eLpNorm_indicator_eq_eLpNorm_restrict hO.measurableSet]
    exact hlu
  have hlgG : Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-G x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    have heq (j : ℕ) : (fun x=>gradient (φ j) x-G x)=O.indicator (fun x=>gradient (φ j) x-g x) := by
      funext x
      by_cases hx : x∈O
      · simp only [G,indicator_of_mem hx]
      · simp only [G,indicator_of_notMem hx,hgφ0 j x hx,sub_zero]
    simp_rw [heq,eLpNorm_indicator_eq_eLpNorm_restrict hO.measurableSet]
    exact hlg
  obtain ⟨v,hvc,hUv,hpointlim⟩ :=
    exists_continuous_representative_and_pointwise_limit_of_strong_smooth_sobolev hn1 hnp hExt.1
      (fun j=>(hφ j).1) (fun j=>(hφ j).2.1) hluG hlgG
  have hunitU : ∀ᵐ x ∂volume,0≤U x ∧ U x≤1 := by
    have ht : ∀ᵐ x ∂volume,x∈O → 0≤u x ∧ u x≤1 := (ae_restrict_iff' hO.measurableSet).mp hunit
    filter_upwards [ht] with x hx
    by_cases hxO : x∈O
    · simpa only [U,indicator_of_mem hxO] using hx hxO
    · simp only [U,indicator_of_notMem hxO]
      exact ⟨le_rfl,zero_le_one⟩
  have hunitV : ∀ᵐ x ∂volume,0≤v x ∧ v x≤1 := by
    filter_upwards [hunitU,hUv] with x hx heq
    rwa [←heq]
  have hvbound := upstream_continuous_global_unit_bounds hvc hunitV
  have hvK (x : Space n) (hx : x∈K) : v x=1 :=
    le_antisymm (hvbound x).2 (ge_of_tendsto (hpointlim x) (Eventually.of_forall (fun j=>(hφ j).2.2.2 x hx)))
  have hvO (x : Space n) (hx : x∉O) : v x=0 := by
    have ht := hpointlim x
    simp only [hφ0 _ x hx] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hUV : u=ᵐ[volume.restrict O] v := by
    filter_upwards [ae_restrict_of_ae hUv,ae_restrict_mem hO.measurableSet] with x hx hxO
    simpa only [U,indicator_of_mem hxO] using hx
  have hgG : g=ᵐ[volume.restrict O] G := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact (indicator_of_mem hx g).symm
  have hvW0 : ZeroBoundarySobolevPair p O v G := hu.congr hUV hgG
  have hvSob : SobolevPair p univ v G := hExt.1.congr
    (by simpa only [Measure.restrict_univ] using hUv) EventuallyEq.rfl
  have hvH : WeakPHarmonicPair p (O\K) v G := hH.congr_ae
    (ae_restrict_of_ae_restrict_of_subset sdiff_subset hUV) (ae_restrict_of_ae_restrict_of_subset sdiff_subset hgG)
  have hvCap : BMCompactCapacityV2.relativeCapacity p K O=ENNReal.ofReal (∫ x in O,‖G x‖^p ∂volume) := by
    rw [hcap]
    congr 1
    exact integral_congr_ae (hgG.fun_comp (fun z=>‖z‖^p))
  have hvApprox : Tendsto (fun j=>eLpNorm (φ j-v) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    have heq (j : ℕ) : eLpNorm (φ j-v) (ENNReal.ofReal p) volume=eLpNorm (φ j-U) (ENNReal.ofReal p) volume :=
      eLpNorm_congr_ae (EventuallyEq.rfl.sub hUv.symm)
    simpa only [heq] using hluG
  exact ⟨v,G,hvc,hvK,hvO,hvbound,hvW0,hvSob,hvH,hvCap,φ,hφ,hvApprox,hlgG⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_continuous_unit_relative_capacity_potential_supercritical
