import UpstreamGreenAnnularLower

/-! A bounded canonical-profile remainder is derived for an actual pointwise
annular limit. The lower barrier comes from genuine weak comparison on the
finite annuli; no bounded remainder or asymptotic constant is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1000000 in
theorem annular_pointwise_limit_has_bounded_canonical_green_remainder
    {n : ℕ} {p : ℝ} (hn : 2≤n) (hnp : (n:ℝ)<p)
    {K : Set (Space n)} (hK : IsCompact K)
    {R : ℕ → ℝ} {G : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n} {v : Space n → ℝ}
    (hR : Tendsto R atTop atTop)
    (hGc : ∀ j,Continuous (G j))
    (hGout : ∀ j x,x∉ball 0 (R j) → G j x=fundamentalRadialValue n (canonicalSphereArea n) p (R j))
    (hH : ∀ j,WeakPHarmonicPair p (ball 0 (R j)\K) (G j) (g j))
    (hB : ∀ j x,0≤G j x ∧ G j x≤fundamentalPotential n (canonicalSphereArea n) p x)
    (hpoint : ∀ x,Tendsto (fun j=>G j x) atTop (𝓝 (v x))) :
    HasBoundedGreenRemainder n (canonicalSphereArea n) p v ∧
      ∃ a : ℝ,0<a ∧ K⊆closedBall (0 : Space n) a ∧ ∀ x,
        fundamentalPotential n (canonicalSphereArea n) p x-
          fundamentalRadialValue n (canonicalSphereArea n) p a≤v x ∧
        v x≤fundamentalPotential n (canonicalSphereArea n) p x := by
  obtain ⟨a,ha,hKa⟩ := hK.isBounded.subset_ball_lt 1 (0 : Space n)
  have ha0 : 0<a := zero_lt_one.trans ha
  have hKc : K⊆closedBall (0 : Space n) a := hKa.trans ball_subset_closedBall
  let F : Space n → ℝ := fundamentalPotential n (canonicalSphereArea n) p
  let c : ℝ := fundamentalRadialValue n (canonicalSphereArea n) p a
  have hbound (x : Space n) : F x-c≤v x ∧ v x≤F x := by
    refine ⟨?_,le_of_tendsto (hpoint x) (Eventually.of_forall (fun j=>(hB j x).2))⟩
    apply ge_of_tendsto (hpoint x)
    filter_upwards [hR.eventually (eventually_gt_atTop ‖x‖)] with j hj
    exact (hH j).fundamental_sub_inner_radius_le_on_ball hn hnp ha0 hKc
      (hGc j) (fun y=>(hB j y).1) (hGout j) x (by simpa only [mem_ball,dist_zero_right] using hj)
  have hrem : HasBoundedGreenRemainder n (canonicalSphereArea n) p v := by
    refine ⟨|c|,abs_nonneg c,Eventually.of_forall (fun x=>?_ )⟩
    apply abs_le.mpr
    have hx := hbound x
    have hc := le_abs_self c
    have hc0 := abs_nonneg c
    change -|c|≤v x-F x ∧ v x-F x≤|c|
    constructor <;> linarith only [hx.1,hx.2,hc,hc0]
  exact ⟨hrem,a,ha0,hKc,hbound⟩

end BMCompactPDE
#print axioms BMCompactPDE.annular_pointwise_limit_has_bounded_canonical_green_remainder
