import EquilibriumFluxMass
import UpstreamGreenAnnularComparison
import UpstreamFundamentalAllp
import UpstreamFundamentalBarrier
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric Bornology
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem compare_decay_on_sphere {n : ℕ} {p R : ℝ} (hn : 2≤n)
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p (closedBall (0:Space n) R)ᶜ u g)
    (hv : WeakPHarmonicPair p (closedBall (0:Space n) R)ᶜ v h)
    (huc : ContinuousOn u (ball (0:Space n) R)ᶜ) (hvc : ContinuousOn v (ball (0:Space n) R)ᶜ)
    (hul : Tendsto u (cocompact _) (𝓝 0)) (hvl : Tendsto v (cocompact _) (𝓝 0))
    (hbound : ∀ x∈sphere (0:Space n) R, u x≤v x) : ∀ x, R≤‖x‖ → u x≤v x := by
  intro x hRx
  rcases hRx.eq_or_lt with he | hx
  · exact hbound x (by simpa only [mem_sphere,dist_zero_right] using he.symm)
  have hdec : Tendsto (fun y => u y-v y) (cocompact _) (𝓝 0) := by simpa using hul.sub hvl
  apply le_of_forall_pos_le_add
  intro ε hε
  have he := hdec.eventually (eventually_lt_nhds hε)
  obtain ⟨r,hr⟩ := closedBall_compl_subset_of_mem_cocompact he (0:Space n)
  let T := max r ‖x‖+1
  let D := ball (0:Space n) T \ closedBall (0:Space n) R
  have hD : IsOpen D := isOpen_ball.sdiff isClosed_closedBall
  have hDb : IsBounded D := isBounded_ball.subset sdiff_subset
  have hsub : D ⊆ (closedBall (0:Space n) R)ᶜ := fun _ h => h.2
  have hcl : closure D ⊆ (ball (0:Space n) R)ᶜ := isOpen_ball.isClosed_compl.closure_subset_iff.mpr
    (hsub.trans (compl_subset_compl.mpr ball_subset_closedBall))
  have hfront (y : Space n) (hy : y∈frontier D) : u y≤v y+ε := by
    have hh := hcl (frontier_subset_closure hy)
    have hyn : R≤‖y‖ := by simpa only [mem_compl_iff,mem_ball,dist_zero_right,not_lt] using hh
    by_cases hyR : ‖y‖=R
    · exact (hbound y (by simpa only [mem_sphere,dist_zero_right] using hyR)).trans (le_add_of_nonneg_right hε.le)
    have houtside : y∉ball (0:Space n) T := fun hyT => (hD.frontier_eq ▸ hy).2
      ⟨hyT,fun hb => hyR (le_antisymm (by simpa only [mem_closedBall,dist_zero_right] using hb) hyn)⟩
    have hny : T≤‖y‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using houtside
    have hfar : y∈(closedBall (0:Space n) r)ᶜ := by
      rw [mem_compl_iff,mem_closedBall,dist_zero_right,not_le]
      exact (lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one).trans_le hny
    have hεy : u y-v y<ε := hr hfar
    linarith
  have hxD : x∈D := by
    refine ⟨?_,?_⟩
    · rw [mem_ball,dist_zero_right]
      exact lt_add_of_le_of_pos (le_max_right _ _) zero_lt_one
    · simpa only [mem_closedBall,dist_zero_right,not_le] using hx
  exact (hu.mono hsub hD).leOn_of_bounded_continuous_boundary_order hn hDb
    ((hv.mono hsub hD).add_const ε) (huc.mono hcl) ((hvc.mono hcl).add continuousOn_const) hfront x hxD

/-- The two normalized radial bounds on any enclosing sphere propagate
to the entire exterior for an actual decaying subcritical weak solution. -/
theorem WeakPHarmonicPair.subcritical_normalized_trapping_on_sphere
    {n : ℕ} {p R : ℝ} (hn : 2≤n) (hpn : p<(n:ℝ)) (hR : 0<R)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p (closedBall (0:Space n) R)ᶜ u g)
    (hc : ContinuousOn u (ball (0:Space n) R)ᶜ)
    (hl : Tendsto u (cocompact _) (𝓝 0)) {a b : ℝ}
    (hs : ∀ y∈sphere (0:Space n) R, a≤R^(((n:ℝ)-p)/(p-1))*u y ∧ R^(((n:ℝ)-p)/(p-1))*u y≤b) :
    ∀ x, R≤‖x‖ → a≤‖x‖^(((n:ℝ)-p)/(p-1))*u x ∧ ‖x‖^(((n:ℝ)-p)/(p-1))*u x≤b := by
  let α := ((n:ℝ)-p)/(p-1)
  have hα : 0<α := div_pos (sub_pos.mpr hpn) (sub_pos.mpr hu.1)
  have hq : (p-(n:ℝ))/(p-1) = -α := by dsimp only [α];ring
  let F : Space n → ℝ := fun x => ‖x‖^(-α)
  have hF : ∃ H, WeakPHarmonicPair p (closedBall (0:Space n) R)ᶜ F H := by
    let t := (p-(n:ℝ))/(p-1)
    have ht : t ≠ 0 := by rw [show t = -α from hq]; exact neg_ne_zero.mpr hα.ne'
    have hz : (closedBall (0:Space n) R)ᶜ ⊆ ({0}:Set (Space n))ᶜ := by
      intro y hy hy0
      have he : y=0 := hy0
      exact hy (he ▸ mem_closedBall_self hR.le)
    have hbase := (weakPHarmonicPair_fundamentalPotential_all_p n zero_lt_one hu.1).mono hz isClosed_closedBall.isOpen_compl
    refine ⟨_, (hbase.smul t).congr_fun ?_⟩
    intro y _
    change t * fundamentalPotential n 1 p y=F y
    simp only [fundamentalPotential,if_neg (ne_of_lt hpn),radialPowerPotential,Real.one_rpow,mul_one]
    change t*(t⁻¹*‖y‖^t)=F y
    rw [←mul_assoc,mul_inv_cancel₀ ht,one_mul,show t = -α from hq]
  have hfc : ContinuousOn F (ball (0:Space n) R)ᶜ := by
    intro y hy
    have hyR : R≤‖y‖ := by simpa only [mem_compl_iff,mem_ball,dist_zero_right,not_lt] using hy
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl (hR.trans_le hyR).ne')).comp
      continuous_norm.continuousAt).continuousWithinAt
  have hfl : Tendsto F (cocompact _) (𝓝 0) := (tendsto_rpow_neg_atTop hα).comp tendsto_norm_cocompact_atTop
  obtain ⟨H,hFH⟩ := hF
  have hconvert {r w : ℝ} (hr : 0<r) :
      (a*r^(-α)≤w ↔ a≤r^α*w) ∧ (w≤b*r^(-α) ↔ r^α*w≤b) := by
    rw [Real.rpow_neg hr.le]
    have hpow := Real.rpow_pos_of_pos hr α
    simp only [←div_eq_mul_inv,div_le_iff₀ hpow,le_div_iff₀ hpow,mul_comm w,iff_self,and_self]
  have hpair (c : ℝ) := hFH.smul c
  have hcl (c : ℝ) : ContinuousOn (c • F) (ball (0:Space n) R)ᶜ := continuousOn_const.smul hfc
  have hlim (c : ℝ) : Tendsto (c • F) (cocompact _) (𝓝 0) := by
    change Tendsto (fun x => c • F x) _ _
    simpa only [smul_zero] using (tendsto_const_nhds (x:=c)).smul hfl
  have hbd (y : Space n) (hy : y∈sphere (0:Space n) R) : (a • F) y ≤ u y ∧ u y ≤ (b • F) y := by
    have he : ‖y‖=R := by simpa only [mem_sphere,dist_zero_right] using hy
    change a*‖y‖^(-α) ≤ u y ∧ u y ≤ b*‖y‖^(-α)
    rw [he]
    exact ⟨(hconvert hR).1.mpr (hs y hy).1,(hconvert hR).2.mpr (hs y hy).2⟩
  intro x hx
  refine ⟨(hconvert (hR.trans_le hx)).1.mp ?_,(hconvert (hR.trans_le hx)).2.mp ?_⟩
  · exact compare_decay_on_sphere hn (hpair a) hu (hcl a) hc (hlim a) hl (fun y hy=>(hbd y hy).1) x hx
  · exact compare_decay_on_sphere hn hu (hpair b) hc (hcl b) hl (hlim b) (fun y hy=>(hbd y hy).2) x hx

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.subcritical_normalized_trapping_on_sphere
