import UpstreamGreenUniformMorrey
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Ascoli

/-! A pointwise convergent continuous Sobolev family above the dimension has
a continuous locally uniform limit, when common actual scalar/gradient Lp
ceilings are supplied. Local Morrey control and equicontinuity are proved;
neither regularity nor uniform convergence of the limit is an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal NNReal ContDiff
namespace BMCompactPDE

private theorem upstream_morrey_pointwise_limit_on_compact
    {X : Type*} [PseudoMetricSpace X] {K : Set X} (hK : IsCompact K)
    {B α : ℝ} (hα : 0<α) {u : ℕ → X → ℝ} {v : X → ℝ}
    (hbound : ∀ j x,x∈K → ∀ y,y∈K → dist (u j x) (u j y)≤B*dist x y^α)
    (hpoint : ∀ x∈K,Tendsto (fun j=>u j x) atTop (𝓝 (v x))) :
    ContinuousOn v K ∧ TendstoUniformlyOn u v atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : ℕ → K → ℝ := fun j x=>u j x
  let f : K → ℝ := fun x=>v x
  have hm : Continuous (fun r : ℝ=>B*r^α) :=
    continuous_const.mul (continuous_id.rpow_const (fun _=>Or.inr hα.le))
  have hm0 : Tendsto (fun r : ℝ=>B*r^α) (𝓝 0) (𝓝 0) := by
    simpa only [Real.zero_rpow (ne_of_gt hα),mul_zero] using hm.tendsto 0
  have heq : UniformEquicontinuous F :=
    Metric.uniformEquicontinuous_of_continuity_modulus (fun r : ℝ=>B*r^α) hm0 F
      (fun x y j=>hbound j x x.2 y y.2)
  have hp : Tendsto F atTop (𝓝 f) := tendsto_pi_nhds.mpr (fun x=>hpoint x x.2)
  have hfc : Continuous f := hp.continuous_of_equicontinuous heq.equicontinuous
  have hu : Tendsto (UniformFun.ofFun ∘ F) atTop (𝓝 (UniformFun.ofFun f)) :=
    (heq.equicontinuous.tendsto_uniformFun_iff_pi atTop f).mpr hp
  have hu' : TendstoUniformly F f atTop := by
    simpa only [Function.comp_def,UniformFun.toFun_ofFun] using
      (UniformFun.tendsto_iff_tendstoUniformly.mp hu)
  exact ⟨continuousOn_iff_continuous_domRestrict.mpr hfc,
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr hu'⟩

/-- Common actual local Lp ceilings and actual pointwise convergence suffice
for a continuous limit and uniform convergence on every compact inner-domain
closure. Holder estimates, limit continuity and uniform convergence are all
derived. The norm ceilings and pointwise convergence remain explicit inputs. -/
theorem continuous_sobolev_family_pointwise_limit_locally_uniform
    {n : ℕ} {p : ℝ} (hn : 1≤n) (hnp : (n : ℝ)<p)
    {U : Set (Space n)} (hU : IsOpen U)
    {M₀ M₁ : ℝ} (hM₀ : 0≤M₀) (hM₁ : 0≤M₁)
    {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n} {v : Space n → ℝ}
    (hSob : ∀ j,SobolevPair p U (u j) (g j)) (hcont : ∀ j,ContinuousOn (u j) U)
    (hMscalar : ∀ j,(eLpNorm (u j) (ENNReal.ofReal p) (volume.restrict U)).toReal≤M₀)
    (hMgradient : ∀ j,(eLpNorm (g j) (ENNReal.ofReal p) (volume.restrict U)).toReal≤M₁)
    (hpoint : ∀ x∈U,Tendsto (fun j=>u j x) atTop (𝓝 (v x))) :
    ContinuousOn v U ∧ ∀ D : Set (Space n),LocalDomain D U →
      TendstoUniformlyOn u v atTop (closure D) := by
  have hp : 0<p := lt_of_le_of_lt (Nat.cast_nonneg n) hnp
  have hα : 0<1-(n : ℝ)/p := sub_pos.mpr ((div_lt_one hp).mpr hnp)
  have hlocal (D : Set (Space n)) (hD : LocalDomain D U) :
      ContinuousOn v (closure D) ∧ TendstoUniformlyOn u v atTop (closure D) := by
    obtain ⟨C,-,hbound⟩ :=
      exists_uniform_local_morrey_coefficient_for_continuous_sobolev_families hn hnp hU hD
    apply upstream_morrey_pointwise_limit_on_compact hD.2.1.isCompact_closure hα
      (hbound M₀ M₁ hM₀ hM₁ u g hSob hcont hMscalar hMgradient)
    intro x hx
    exact hpoint x (hD.2.2 hx)
  refine ⟨?_,fun D hD=>(hlocal D hD).2⟩
  intro x hx
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hU x hx
  let D : Set (Space n) := ball x (ρ/2)
  have hD : LocalDomain D U := by
    refine ⟨isOpen_ball,isBounded_ball,?_⟩
    exact closure_ball_subset_closedBall.trans
      ((closedBall_subset_ball (by linarith only [hρ] : ρ/2<ρ)).trans hball)
  have hxD : x∈D := mem_ball_self (half_pos hρ)
  have hc : ContinuousAt v x := (hlocal D hD).1.continuousAt
    (mem_of_superset (hD.1.mem_nhds hxD) subset_closure)
  exact hc.continuousWithinAt

end BMCompactPDE
#print axioms BMCompactPDE.continuous_sobolev_family_pointwise_limit_locally_uniform
