import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-! Direct minimization by a proved midpoint energy gap.
No reflexivity, compact sublevel set, minimizer, or existence axiom is an input.
Actual nonlinear energy must separately satisfy continuity, lower boundedness
and the displayed quantitative midpoint inequality before this theorem applies. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace BMCompactBanach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cauchySeq_of_midpoint_gap {K : Set E} (hK : Convex ℝ K)
    {f : E → ℝ} {d : ℝ} (hlow : ∀ z∈K,d≤f z)
    (hgap : ∀ ε : ℝ,0<ε → ∃ κ : ℝ,0<κ ∧ ∀ x∈K,∀ y∈K,
      ε≤‖x-y‖ → f ((1/2 : ℝ) • x+(1/2 : ℝ) • y)≤(f x+f y)/2-κ)
    {w : ℕ → E} (hw : ∀ j,w j∈K) (hlim : Tendsto (f ∘ w) atTop (𝓝 d)) :
    CauchySeq w := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨κ,hκ,hg⟩ := hgap ε hε
  have he := hlim.eventually (gt_mem_nhds (lt_add_of_pos_right d (half_pos hκ)))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,?_⟩
  intro j hj k hk
  rw [dist_eq_norm]
  by_contra hdist
  have hsep : ε≤‖w j-w k‖ := le_of_not_gt hdist
  have hmidmem := hK (hw j) (hw k)
    (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  have hm := hlow _ hmidmem
  have hg' := hg (w j) (hw j) (w k) (hw k) hsep
  have hj' : f (w j)<d+κ/2 := hN j hj
  have hk' : f (w k)<d+κ/2 := hN k hk
  linarith

/-- Direct existence for continuous lower-bounded energy on a nonempty complete
convex set, with a genuine uniform positive midpoint deficit at separated points. -/
theorem exists_minimum_of_complete_midpoint_gap {K : Set E} (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hK : Convex ℝ K) {f : E → ℝ}
    (hf : ContinuousOn f K) (hbdd : BddBelow (f '' K))
    (hgap : ∀ ε : ℝ,0<ε → ∃ κ : ℝ,0<κ ∧ ∀ x∈K,∀ y∈K,
      ε≤‖x-y‖ → f ((1/2 : ℝ) • x+(1/2 : ℝ) • y)≤(f x+f y)/2-κ) :
    ∃ v∈K,∀ z∈K,f v≤f z := by
  let : Nonempty K := hne.to_subtype
  let d := ⨅ z : K,f z
  have hrange : Set.range (fun z : K=>f z)=f '' K := by
    ext a
    simp only [mem_range,mem_image]
    constructor
    · rintro ⟨⟨z,hz⟩,rfl⟩;exact ⟨z,hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩;exact ⟨⟨z,hz⟩,rfl⟩
  have hbd : BddBelow (Set.range (fun z : K=>f z)) := hrange ▸ hbdd
  have hlow : ∀ z∈K,d≤f z := fun z hz=>ciInf_le hbd (⟨z,hz⟩ : K)
  have hseq : ∃ w : ℕ → K,∀ j,f (w j)<d+1/((j : ℝ)+1) := by
    have he (j : ℕ) : d<d+1/((j : ℝ)+1) := lt_add_of_pos_right d Nat.one_div_pos_of_nat
    choose w hw using (fun j=>exists_lt_of_ciInf_lt (he j))
    exact ⟨w,hw⟩
  obtain ⟨w,hw⟩ := hseq
  have hlim : Tendsto (fun j=>f (w j)) atTop (𝓝 d) := by
    have ht : Tendsto (fun j : ℕ=>d+1/((j : ℝ)+1)) atTop (𝓝 d) := by
      simpa only [add_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>d) atTop (𝓝 d)).add tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun j=>hlow (w j) (w j).2) (fun j=>(hw j).le)
  have hc := cauchySeq_of_midpoint_gap hK hlow hgap (fun j=>(w j).2) hlim
  obtain ⟨v,hv,hvlim⟩ := cauchySeq_tendsto_of_isComplete hcomplete (fun j=>(w j).2) hc
  have hvf : Tendsto (fun j=>f (w j)) atTop (𝓝 (f v)) :=
    (hf v hv).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hvlim,Eventually.of_forall (fun j=>(w j).2)⟩)
  have he : f v=d := tendsto_nhds_unique hvf hlim
  exact ⟨v,hv,fun z hz=>he.le.trans (hlow z hz)⟩

theorem minimum_unique_of_midpoint_gap {K : Set E} (hK : Convex ℝ K)
    {f : E → ℝ}
    (hgap : ∀ ε : ℝ,0<ε → ∃ κ : ℝ,0<κ ∧ ∀ x∈K,∀ y∈K,
      ε≤‖x-y‖ → f ((1/2 : ℝ) • x+(1/2 : ℝ) • y)≤(f x+f y)/2-κ)
    {v w : E} (hv : v∈K) (hw : w∈K)
    (hvm : ∀ z∈K,f v≤f z) (hwm : ∀ z∈K,f w≤f z) : v=w := by
  by_contra hne
  obtain ⟨κ,hκ,hg⟩ := hgap ‖v-w‖ (norm_sub_pos_iff.mpr hne)
  have hm := hvm _ (hK hv hw (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)+1/2=1))
  have hg' := hg v hv w hw le_rfl
  have he : f v=f w := le_antisymm (hvm w hw) (hwm v hv)
  rw [←he] at hg'
  linarith

end BMCompactBanach
#print axioms BMCompactBanach.cauchySeq_of_midpoint_gap
#print axioms BMCompactBanach.exists_minimum_of_complete_midpoint_gap
#print axioms BMCompactBanach.minimum_unique_of_midpoint_gap
