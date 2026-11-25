import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Module

/-! A genuine near-minimizer diameter estimate in uniformly convex Banach geometry.
This is a foundation for nonlinear variational existence, not an assumption
that the actual Lp gradient space already has the requisite geometry. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace BMCompactBanach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [UniformConvexSpace E]

theorem uniformlyConvex_near_minimum_diameter {K : Set E} (hK : Convex ℝ K)
    (u : E) {d : ℝ} (hd : 0≤d) (hlow : ∀ z∈K,d≤‖u-z‖)
    {ε : ℝ} (hε : 0<ε) :
    ∃ η : ℝ, 0<η ∧ ∀ x∈K, ∀ y∈K,
      ‖u-x‖≤d+η → ‖u-y‖≤d+η → ‖x-y‖<ε := by
  by_cases hd0 : d=0
  · refine ⟨ε/4,by positivity,?_⟩
    intro x hx y hy hxn hyn
    have he : x-y=-(u-x)+(u-y) := by abel
    have ht := norm_add_le (-(u-x)) (u-y)
    rw [←he,norm_neg] at ht
    rw [hd0] at hxn hyn
    linarith
  have hdp : 0<d := lt_of_le_of_ne hd (Ne.symm hd0)
  have hR : 0<d+1 := by positivity
  obtain ⟨κ,hκ,hmod⟩ := exists_forall_closed_ball_dist_add_le_two_sub E (div_pos hε hR)
  let k := min κ 1
  have hk : 0<k := lt_min hκ zero_lt_one
  have hkκ : k≤κ := min_le_left _ _
  have hk1 : k≤1 := min_le_right _ _
  let η := min (1/2 : ℝ) (k*d/8)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1/2 := min_le_left _ _
  have hηkd : η≤k*d/8 := min_le_right _ _
  refine ⟨η,hη,?_⟩
  intro x hx y hy hxn hyn
  by_contra hdist
  have hxy : ε≤‖x-y‖ := le_of_not_gt hdist
  let q := d+η
  have hq : 0<q := add_pos hdp hη
  have hqR : q≤d+1 := by dsimp only [q]; linarith
  let a := q⁻¹ • (u-x)
  let b := q⁻¹ • (u-y)
  have ha : ‖a‖≤1 := by
    dsimp only [a]
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hq.le)]
    exact (mul_le_mul_of_nonneg_left hxn (inv_nonneg.mpr hq.le)).trans_eq
      (inv_mul_cancel₀ hq.ne')
  have hb : ‖b‖≤1 := by
    dsimp only [b]
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hq.le)]
    exact (mul_le_mul_of_nonneg_left hyn (inv_nonneg.mpr hq.le)).trans_eq
      (inv_mul_cancel₀ hq.ne')
  have hab : ‖a-b‖=q⁻¹*‖x-y‖ := by
    dsimp only [a,b]
    rw [←smul_sub,norm_smul_of_nonneg (inv_nonneg.mpr hq.le)]
    congr 1
    rw [sub_sub_sub_cancel_left,norm_sub_rev]
  have heps : ε/(d+1)≤‖a-b‖ := by
    rw [hab,←div_eq_inv_mul]
    exact (div_le_div_of_nonneg_left hε.le hq hqR).trans
      (div_le_div_of_nonneg_right hxy hq.le)
  have hm := hmod ha hb heps
  have hsum : ‖(u-x)+(u-y)‖≤(2-k)*q := by
    have he : ‖a+b‖=q⁻¹*‖(u-x)+(u-y)‖ := by
      dsimp only [a,b]
      rw [←smul_add,norm_smul_of_nonneg (inv_nonneg.mpr hq.le)]
    rw [he,←div_eq_inv_mul] at hm
    exact ((div_le_iff₀ hq).mp hm).trans
      (mul_le_mul_of_nonneg_right (by linarith) hq.le)
  have hmidmem : (1/2 : ℝ) • x+(1/2 : ℝ) • y∈K :=
    hK hx hy (by norm_num) (by norm_num) (by norm_num)
  have hmid := hlow _ hmidmem
  have he : u-((1/2 : ℝ) • x+(1/2 : ℝ) • y)=
      (1/2 : ℝ) • ((u-x)+(u-y)) := by module
  rw [he,norm_smul_of_nonneg (by norm_num : (0 : ℝ)≤1/2)] at hmid
  have hneg : (2-k)*q<2*d := by
    dsimp only [q]
    have hkd : 0<k*d := mul_pos hk hdp
    have hkη : 0≤k*η := mul_nonneg hk.le hη.le
    nlinarith
  linarith

theorem cauchySeq_of_tendsto_minimum_norm {K : Set E} (hK : Convex ℝ K)
    (u : E) {d : ℝ} (hd : 0≤d) (hlow : ∀ z∈K,d≤‖u-z‖)
    {w : ℕ → E} (hw : ∀ j,w j∈K)
    (hlim : Tendsto (fun j=>‖u-w j‖) atTop (𝓝 d)) : CauchySeq w := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨η,hη,hclose⟩ := uniformlyConvex_near_minimum_diameter hK u hd hlow hε
  have he := hlim.eventually (gt_mem_nhds (lt_add_of_pos_right d hη))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,?_⟩
  intro j hj k hk
  rw [dist_eq_norm]
  exact hclose (w j) (hw j) (w k) (hw k) (hN j hj).le (hN k hk).le

/-- Nearest points in a nonempty complete convex set in any uniformly convex
real normed space. Uniform convexity is a genuine class input, not an Lp axiom. -/
theorem exists_nearestPoint_of_complete_convex {K : Set E} (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hK : Convex ℝ K) (u : E) :
    ∃ v∈K, ∀ z∈K, ‖u-v‖≤‖u-z‖ := by
  let : Nonempty K := hne.to_subtype
  let d := ⨅ z : K, ‖u-z‖
  have hd : 0≤d := le_ciInf (fun _=>norm_nonneg _)
  have hlow : ∀ z∈K,d≤‖u-z‖ := fun z hz =>
    ciInf_le ⟨0,Set.forall_mem_range.mpr (fun _=>norm_nonneg _)⟩ (⟨z,hz⟩ : K)
  have hseq : ∃ w : ℕ → K, ∀ j, ‖u-w j‖<d+1/((j : ℝ)+1) := by
    have he (j : ℕ) : d<d+1/((j : ℝ)+1) :=
      lt_add_of_pos_right d Nat.one_div_pos_of_nat
    choose w hw using (fun j=>exists_lt_of_ciInf_lt (he j))
    exact ⟨w,hw⟩
  obtain ⟨w,hw⟩ := hseq
  have hlim : Tendsto (fun j=>‖u-w j‖) atTop (𝓝 d) := by
    have ht : Tendsto (fun j : ℕ => d+1/((j : ℝ)+1)) atTop (𝓝 d) := by
      simpa only [add_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>d) atTop (𝓝 d)).add tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun j=>hlow (w j) (w j).2) (fun j=>(hw j).le)
  have hc := cauchySeq_of_tendsto_minimum_norm hK u hd hlow
    (fun j=>(w j).2) hlim
  obtain ⟨v,hv,hvlim⟩ := cauchySeq_tendsto_of_isComplete hcomplete
    (fun j=>(w j).2) hc
  have hvnorm : Tendsto (fun j=>‖u-w j‖) atTop (𝓝 ‖u-v‖) := by
    exact (continuous_const.sub continuous_id).norm.continuousAt.tendsto.comp hvlim
  have he : ‖u-v‖=d := tendsto_nhds_unique hvnorm hlim
  exact ⟨v,hv,fun z hz => he.le.trans (hlow z hz)⟩

end BMCompactBanach
#print axioms BMCompactBanach.uniformlyConvex_near_minimum_diameter
#print axioms BMCompactBanach.cauchySeq_of_tendsto_minimum_norm
#print axioms BMCompactBanach.exists_nearestPoint_of_complete_convex
