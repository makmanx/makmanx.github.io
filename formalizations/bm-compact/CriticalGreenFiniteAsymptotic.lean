import CriticalGreenSphereClosure
import CriticalGreenRescaledFamily
import UniformCriticalHolder
import CompactGradientOscillation
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.MetricSpace.Equicontinuity

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace BMCompactPDE

private theorem equicontinuous_remainders_of_holder
    {n : ℕ} {C : Set (Space n)} {V : ℕ → Space n → ℝ} {F : Space n → ℝ}
    {L α : ℝ} (hα : 0<α) (hF : ContinuousOn F C)
    (hV : ∀ j x, x∈C → ∀ y, y∈C → dist (V j x) (V j y) ≤ L*dist x y^α) :
    Equicontinuous (fun (j : ℕ) (x : C) => V j x.val-F x.val) := by
  have hFc : Continuous (fun x : C => F x.val) := continuousOn_iff_continuous_domRestrict.mp hF
  intro x
  let b := fun y : C => L*dist x y^α + dist (F x.val) (F y.val)
  have hb : Continuous b :=
    (continuous_const.mul ((continuous_const.dist continuous_id).rpow_const (fun _=>Or.inr hα.le))).add
      (continuous_const.dist hFc)
  have hb0 : b x = 0 := by simp only [b,dist_self,Real.zero_rpow hα.ne',mul_zero,add_zero]
  apply Metric.equicontinuousAt_of_continuity_modulus b (by simpa only [hb0] using hb.tendsto x)
  exact Eventually.of_forall (fun y j => by
    have hh := hV j x x.property y y.property
    simp only [Real.dist_eq] at hh
    change |(V j x.val-F x.val)-(V j y.val-F y.val)| ≤ L*dist x.val y.val^α+|F x.val-F y.val|
    rw [show (V j x.val-F x.val)-(V j y.val-F y.val) = (V j x.val-V j y.val) + -(F x.val-F y.val) by ring]
    exact (abs_add_le _ _).trans <| by simpa only [abs_neg] using add_le_add hh (le_refl |F x.val-F y.val|))

/-- At the critical exponent every actual exterior Green function has one finite
logarithmic constant at infinity. Only a bounded remainder is part of the input. -/
theorem IsExteriorGreen.existsUnique_finite_critical_asymptotic
    {n : ℕ} {σ : ℝ} {K : Set (Space n)} {u : Space n → ℝ}
    (hu : IsExteriorGreen n σ n K u) :
    ∃! c : ℝ, HasGreenAsymptotic n σ n u c := by
  let F := fundamentalPotential n σ (n:ℝ) (E:=Space n)
  let U := radialAnnulusAt n 0 2 7
  let D := radialAnnulusAt n 0 3 5
  let C := closure D
  let Q := sphere (0:Space n) 4
  have hp : 1<(n:ℝ) := hu.1
  have hn : 1<n := by exact_mod_cast hp
  have hD : LocalDomain D U := by
    refine ⟨isOpen_radialAnnulusAt _ _ _ _,isBounded_radialAnnulusAt _ _ _ _,?_⟩
    intro x hx
    have hbounds := bounds_of_mem_closure_radialAnnulusAt n (0:Space n) 3 5 hx
    exact ⟨(by norm_num : (2:ℝ)<3).trans_le hbounds.1,hbounds.2.trans_lt (by norm_num)⟩
  have hCU : C⊆U := hD.2.2
  have hFc : ContinuousOn F C := by
    intro x hx
    have hlower : (2:ℝ)<‖x‖ := by simpa only [dist_zero_right] using (hCU hx).1
    exact (contDiffAt_fundamentalPotential n σ (n:ℝ)
      (norm_pos_iff.mp (lt_trans (by norm_num : (0:ℝ)<2) hlower))).continuousAt.continuousWithinAt
  have hrank : 1 < Module.rank ℝ (Space n) := Module.one_lt_rank_of_one_lt_finrank (by
    simpa only [Space,finrank_euclideanSpace,Fintype.card_fin] using hn)
  have hQ : IsPreconnected Q := isPreconnected_sphere hrank 0 4
  have hQD : Q ⊆ D := by
    intro x hx
    have hx' : dist x 0=4 := hx
    change (3:ℝ)<dist x 0 ∧ dist x 0<5
    rw [hx']
    norm_num
  obtain ⟨R,V,Γ,H,hR,hRt,hVh,hVs,hVc,⟨B,hB,hVb⟩,⟨M,N,hM,hN,hMN⟩,hid,hSob,hdec⟩ :=
    hu.exists_critical_rescaled_family_with_vanishing_defect
  obtain ⟨L,_,hholder⟩ := exists_uniform_critical_holder_of_weak_source_family
    (fun j=>(hVh j).source_zero) hVs (show 2≤n by omega) (isBounded_radialAnnulusAt _ _ _ _)
    hM hN (fun j=>(hMN j).1) (fun j=>(hMN j).2) (fun j=>(hVc j).continuousOn)
    hB (fun j x hx=>(hVb j x hx).1) hD
  have heq := equicontinuous_remainders_of_holder
    (show 0<1/(n:ℝ) from one_div_pos.mpr (zero_lt_one.trans hp)) hFc hholder
  have hosc := exists_subsequence_small_oscillation_on_connected hp hQ hQD hD.1 subset_closure
    hD.2.1.isCompact_closure hCU hSob heq
    (fun j x hx=>by rw [hid j x (hCU hx)];exact (hVb j x (hCU hx)).2) hdec
  obtain ⟨c,hc⟩ := hu.exists_finite_critical_asymptotic_of_rescaled_sphere_oscillation hR hRt (by
    intro ε hε m
    obtain ⟨j,hj,hos⟩ := hosc ε hε m
    refine ⟨j,hj,?_⟩
    intro x y hx hy
    have hxs : x∈Q := by simpa only [Q,mem_sphere,dist_zero_right] using hx
    have hys : y∈Q := by simpa only [Q,mem_sphere,dist_zero_right] using hy
    simpa only [hid j x (hCU (subset_closure (hQD hxs))),hid j y (hCU (subset_closure (hQD hys)))] using
      hos x hxs y hys)
  exact ⟨c,hc,fun d hd=>HasGreenAsymptotic.unique_of_dimension (by omega) hd hc⟩

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.existsUnique_finite_critical_asymptotic
