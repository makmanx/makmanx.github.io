import UpstreamGreenAnnularTranslate

/-! Zero obstacle trace and global continuity of an actual annular pointwise
limit. The shifted upper barriers are DERIVED from the actual weak annular
problems; boundary continuity of the limit is not an input. Interior continuity
and pointwise convergence remain explicit here and are constructed separately. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1000000 in
theorem continuous_annular_pointwise_limit_with_zero_obstacle
    {n : ℕ} {p : ℝ} (hn : 2≤n) (hnp : (n:ℝ)<p)
    {K : Set (Space n)} (hK : IsCompact K)
    {R : ℕ → ℝ} {G : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n} {v : Space n → ℝ}
    (hR : Tendsto R atTop atTop)
    (hGc : ∀ j,Continuous (G j)) (hGK : ∀ j x,x∈K → G j x=0)
    (hGout : ∀ j x,x∉ball 0 (R j) → G j x=fundamentalRadialValue n (canonicalSphereArea n) p (R j))
    (hH : ∀ j,WeakPHarmonicPair p (ball 0 (R j)\K) (G j) (g j))
    (hG0 : ∀ j x,0≤G j x)
    (hpoint : ∀ x,Tendsto (fun j=>G j x) atTop (𝓝 (v x)))
    (hvext : ContinuousOn v Kᶜ) :
    Continuous v ∧ (∀ x∈K,v x=0) ∧
      ∀ a∈K,∀ x,0≤v x ∧ v x≤fundamentalPotential n (canonicalSphereArea n) p (x-a) := by
  have hn1 : 1<n := lt_of_lt_of_le (by decide : 1<2) hn
  have hnr : 1<(n:ℝ) := by exact_mod_cast hn1
  let F : Space n → ℝ := fundamentalPotential n (canonicalSphereArea n) p
  have hv0 (x : Space n) : 0≤v x := ge_of_tendsto (hpoint x) (Eventually.of_forall (fun j=>hG0 j x))
  have hvK (a : Space n) (ha : a∈K) : v a=0 := by
    have hz : Tendsto (fun j=>G j a) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (Eventually.of_forall (fun j=>(hGK j a ha).symm))
    exact tendsto_nhds_unique (hpoint a) hz
  have hupper (a : Space n) (ha : a∈K) (x : Space n) : v x≤F (x-a) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨T,-,hT⟩ := exists_radius_threshold_annular_translated_fundamental_upper_bound hn hnp hK ha hε
    have htail : ∀ᶠ j in atTop,G j x≤F (x-a)+ε := by
      filter_upwards [hR.eventually (eventually_gt_atTop (max T ‖x‖))] with j hj
      have hTj : T≤R j := (le_max_left _ _).trans hj.le
      have hxj : x∈ball (0 : Space n) (R j) := by
        simpa only [mem_ball,dist_zero_right] using ((le_max_right _ _).trans_lt hj)
      exact hT (R j) hTj (G j) (g j) (hH j) (hGc j) (hGK j) (hGout j) x hxj
    exact le_of_tendsto (hpoint x) htail
  have hFzero : F 0=0 := by
    have hq : 0<(p-(n:ℝ))/(p-1) := div_pos (sub_pos.mpr hnp) (sub_pos.mpr (hnr.trans hnp))
    simp [F,fundamentalPotential,ne_of_gt hnp,radialPowerPotential,Real.zero_rpow (ne_of_gt hq)]
  have hcont : Continuous v := by
    rw [continuous_iff_continuousAt]
    intro a
    by_cases ha : a∈K
    · have hFc : Continuous (fun x=>F (x-a)) :=
        (continuous_fundamentalPotential_supercritical n _ hnr hnp).comp (continuous_id.sub continuous_const)
      have hFlim : Tendsto (fun x=>F (x-a)) (𝓝 a) (𝓝 0) := by
        simpa only [sub_self,hFzero] using hFc.tendsto a
      have hvlim : Tendsto v (𝓝 a) (𝓝 0) := by
        apply tendsto_const_nhds.squeeze' hFlim
        · exact Eventually.of_forall hv0
        · exact Eventually.of_forall (hupper a ha)
      simpa only [ContinuousAt,hvK a ha] using hvlim
    · exact hvext.continuousAt (hK.isClosed.isOpen_compl.mem_nhds ha)
  exact ⟨hcont,hvK,fun a ha x=>⟨hv0 x,hupper a ha x⟩⟩

end BMCompactPDE
#print axioms BMCompactPDE.continuous_annular_pointwise_limit_with_zero_obstacle
