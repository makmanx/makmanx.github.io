import UpstreamBoundaryRelativeClamp
import UpstreamCriticalContinuity
import ExteriorCondenserConstruction

/-! Actual all-exponent selected bounded relative capacitary potentials.
Only interior continuity on O\K is concluded at this stage; true global AE
patching retains W0, energy, supplied gradient and both admissible limits.
No pointwise obstacle trace or continuity at the outer boundary is asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1200000 in
theorem exists_selected_unit_bounded_relative_capacity_potential_allp
    {n : ℕ} {p : ℝ} (hp : 1<p) (hn : 2≤n) {K O : Set (Space n)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O) (hOb : Bornology.IsBounded O) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      ContinuousOn u (O\K) ∧ (∀ x∉O,u x=0) ∧ (∀ x∈O\K,0≤u x ∧ u x≤1) ∧
      ZeroBoundarySobolevPair p O u g ∧ SobolevPair p univ u g ∧
      WeakPHarmonicPair p (O\K) u g ∧ (∀ᵐ x ∂volume,0≤u x ∧ u x≤1) ∧
      BMCompactCapacityV2.relativeCapacity p K O=ENNReal.ofReal (∫ x in O,‖g x‖^p ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K O (φ j)) ∧
        Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
        Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  classical
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
  let D : Set (Space n) := O\K
  have hD : IsOpen D := hO.sdiff hK.isClosed
  obtain ⟨v,hvc,huv,-⟩ := hH.source_zero.exists_continuous_weak_representative_allp hn
  let V : Space n → ℝ := fun x=>if x∈D then v x else U x
  have hlocal : ∀ᵐ x ∂volume,x∈D → u x=v x :=
    (ae_restrict_iff' hD.measurableSet).mp huv
  have hUV : U=ᵐ[volume] V := by
    filter_upwards [hlocal] with x hx
    by_cases hxD : x∈D
    · simp only [V,if_pos hxD,U,indicator_of_mem hxD.1]
      exact hx hxD
    · simp only [V,if_neg hxD]
  have hVv : EqOn V v D := fun x hx=>if_pos hx
  have hVc : ContinuousOn V D := hvc.congr hVv
  have hunitU : ∀ᵐ x ∂volume,0≤U x ∧ U x≤1 := by
    have ht : ∀ᵐ x ∂volume,x∈O → 0≤u x ∧ u x≤1 := (ae_restrict_iff' hO.measurableSet).mp hunit
    filter_upwards [ht] with x hx
    by_cases hxO : x∈O
    · simpa only [U,indicator_of_mem hxO] using hx hxO
    · simp only [U,indicator_of_notMem hxO]
      exact ⟨le_rfl,zero_le_one⟩
  have hunitV : ∀ᵐ x ∂volume,0≤V x ∧ V x≤1 := by
    filter_upwards [hunitU,hUV] with x hx heq
    rwa [←heq]
  have hlow : (fun x=>max (-V x) 0)=ᵐ[volume.restrict D] (fun _=>0) := by
    filter_upwards [ae_restrict_of_ae hunitV] with x hx
    exact max_eq_right (neg_nonpos.mpr hx.1)
  have hupp : (fun x=>max (V x-1) 0)=ᵐ[volume.restrict D] (fun _=>0) := by
    filter_upwards [ae_restrict_of_ae hunitV] with x hx
    exact max_eq_right (sub_nonpos.mpr hx.2)
  have hl := Measure.eqOn_open_of_ae_eq hlow hD
    ((show Continuous (fun t : ℝ=>max (-t) 0) by fun_prop).comp_continuousOn hVc) continuousOn_const
  have hh := Measure.eqOn_open_of_ae_eq hupp hD
    ((show Continuous (fun t : ℝ=>max (t-1) 0) by fun_prop).comp_continuousOn hVc) continuousOn_const
  have hVB (x : Space n) (hx : x∈D) : 0≤V x ∧ V x≤1 :=
    ⟨neg_nonpos.mp ((le_max_left (-V x) 0).trans_eq (hl hx)),
      sub_nonpos.mp ((le_max_left (V x-1) 0).trans_eq (hh hx))⟩
  have hVO (x : Space n) (hx : x∉O) : V x=0 := by
    have hxD : x∉D := fun hh=>hx hh.1
    simp only [V,if_neg hxD,U,indicator_of_notMem hx]
  have huV : u=ᵐ[volume.restrict O] V := by
    filter_upwards [ae_restrict_of_ae hUV,ae_restrict_mem hO.measurableSet] with x hx hxO
    simpa only [U,indicator_of_mem hxO] using hx
  have hgG : g=ᵐ[volume.restrict O] G := by
    filter_upwards [ae_restrict_mem hO.measurableSet] with x hx
    exact (indicator_of_mem hx g).symm
  have hVW : ZeroBoundarySobolevPair p O V G := hu.congr huV hgG
  have hVS : SobolevPair p univ V G := hExt.1.congr
    (by simpa only [Measure.restrict_univ] using hUV) EventuallyEq.rfl
  have hVH : WeakPHarmonicPair p D V G := hH.congr_ae
    (ae_restrict_of_ae_restrict_of_subset sdiff_subset huV)
    (ae_restrict_of_ae_restrict_of_subset sdiff_subset hgG)
  have hcapV : BMCompactCapacityV2.relativeCapacity p K O=ENNReal.ofReal (∫ x in O,‖G x‖^p ∂volume) := by
    rw [hcap]
    congr 1
    exact integral_congr_ae (hgG.fun_comp (fun z=>‖z‖^p))
  have hluV : Tendsto (fun j=>eLpNorm (φ j-V) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    have heq (j : ℕ) : eLpNorm (φ j-V) (ENNReal.ofReal p) volume=eLpNorm (φ j-U) (ENNReal.ofReal p) volume :=
      eLpNorm_congr_ae (EventuallyEq.rfl.sub hUV.symm)
    simpa only [heq] using hluG
  exact ⟨V,G,hVc,hVO,hVB,hVW,hVS,hVH,hunitV,hcapV,φ,hφ,hluV,hlgG⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_selected_unit_bounded_relative_capacity_potential_allp
