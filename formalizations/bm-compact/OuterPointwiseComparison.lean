import OuterNeighborhoodPotential

noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology Pointwise
namespace BMCompactPDE

/-- The liminf uses full neighborhoods, including their center, as in the
paper's increasing limit of ball infima. All three functions are regularized. -/
theorem min_comparison_lower_regularizations {n : ℕ} {t : ℝ}
    {u v w : Space n → ℝ} (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hw : ∀ x, w x ≤ 1)
    (h : ∀ y z, min (u y) (v z) ≤ w (t • y + (1 - t) • z)) (y z : Space n) :
    min (liminf u (𝓝 y)) (liminf v (𝓝 z)) ≤ liminf w (𝓝 (t • y + (1-t) • z)) := by
  let x := t • y + (1-t) • z
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  have hu' := eventually_lt_of_lt_liminf (lt_min_iff.mp hc).1
    (show (𝓝 y).IsBoundedUnder (· ≥ ·) u from ⟨0, (show ∀ᶠ k in 𝓝 y, 0 ≤ u k from Eventually.of_forall hu)⟩)
  have hv' := eventually_lt_of_lt_liminf (lt_min_iff.mp hc).2
    (show (𝓝 z).IsBoundedUnder (· ≥ ·) v from ⟨0, (show ∀ᶠ k in 𝓝 z, 0 ≤ v k from Eventually.of_forall hv)⟩)
  have shift (b : Space n) : Tendsto (fun a : Space n => b + (a-x)) (𝓝 x) (𝓝 b) := by
    have hcont : Continuous (fun a : Space n => b + (a-x)) := by fun_prop
    have hh := hcont.tendsto x
    change Tendsto (fun a : Space n => b+(a-x)) (𝓝 x) (𝓝 (b+(x-x))) at hh
    rwa [sub_self,add_zero] at hh
  apply le_liminf_of_le (isCoboundedUnder_ge_of_le (𝓝 x) hw)
  filter_upwards [(shift y).eventually hu',(shift z).eventually hv'] with a ha hb
  have hid : t • (y+(a-x)) + (1-t) • (z+(a-x)) = a := by
    dsimp only [x]; module
  rw [←hid]
  exact (le_min ha.le hb.le).trans (h _ _)

/-- For arbitrary compact inputs, the sole comparison premise is the
pointwise PDE inequality for the genuine positive-radius neighborhood
potentials. Both claims of C(b) then pass to constructed outer limits. -/
theorem theoremC_subcritical_outer_of_neighborhood_comparison
    {n : ℕ} {p t : ℝ} (hp : 1 < p) (hpn : p < (n:ℝ))
    {E F : Set (Space n)} (hE : IsCompact E) (hF : IsCompact F)
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hregular : ∀ r : Ioi (0:ℝ),
      ∀ U : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val E),
      ∀ V : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val F),
      ∀ W : ContinuousUnitCapacityData p (t • BMCompact.closedNeighborhood r.val E +
        (1-t) • BMCompact.closedNeighborhood r.val F),
      ∀ y z, min (U.scalar y) (V.scalar z) ≤ W.scalar (t • y + (1-t) • z)) :
    ∃ U : (r : Ioi (0:ℝ)) → ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val E),
    ∃ V : (r : Ioi (0:ℝ)) → ContinuousUnitCapacityData p (BMCompact.closedNeighborhood r.val F),
    ∃ W : (r : Ioi (0:ℝ)) → ContinuousUnitCapacityData p
      (BMCompact.closedNeighborhood r.val (t • E + (1-t) • F)),
    ∃ u v w : Space n → ℝ,
      (∀ x, Tendsto (fun r => (U r).scalar x) atBot (𝓝 (u x))) ∧
      (∀ x, Tendsto (fun r => (V r).scalar x) atBot (𝓝 (v x))) ∧
      (∀ x, Tendsto (fun r => (W r).scalar x) atBot (𝓝 (w x))) ∧
      (∀ y z, min (u y) (v z) ≤ w (t • y + (1-t) • z)) ∧
      ∀ y z, min (liminf u (𝓝 y)) (liminf v (𝓝 z)) ≤
        liminf w (𝓝 (t • y + (1-t) • z)) := by
  classical
  let _ : Nonempty (Ioi (0:ℝ)) := ⟨⟨(1:ℝ),(by norm_num : (0:ℝ)<1)⟩⟩
  obtain ⟨U,u,_,hU,_,bu,_⟩ := exists_subcritical_outer_neighborhood_potential hp hpn hE
  obtain ⟨V,v,_,hV,_,bv,_⟩ := exists_subcritical_outer_neighborhood_potential hp hpn hF
  obtain ⟨W,w,_,hW,_,bw,_⟩ := exists_subcritical_outer_neighborhood_potential hp hpn
    ((hE.smul t).add (hF.smul (1-t)))
  have hpt (y z : Space n) : min (u y) (v z) ≤ w (t • y + (1-t) • z) := by
    apply le_of_tendsto_of_tendsto' ((hU y).min (hV z)) (hW _)
    intro r
    have hc := hregular r (U r) (V r)
    rw [BMCompact.weighted_closedNeighborhood hE hF ht ht1 r.property.le] at hc
    exact hc (W r) y z
  exact ⟨U,V,W,u,v,w,hU,hV,hW,hpt,
    min_comparison_lower_regularizations (fun x => (bu x).1) (fun x => (bv x).1)
      (fun x => (bw x).2) hpt⟩

end BMCompactPDE
#print axioms BMCompactPDE.min_comparison_lower_regularizations
#print axioms BMCompactPDE.theoremC_subcritical_outer_of_neighborhood_comparison
