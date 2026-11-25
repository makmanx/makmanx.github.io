import UpstreamGreenAnnularConstruction
import RadialTranslationLimit
import GradientAnalyticBatch

/-! Actual shifted-pole comparison for large annuli. The threshold is derived
from the genuine translation asymptotic of the explicit profile; the input
weak function needs no shifted-profile bound or boundary regularity beyond its
already constructed continuity and exact Dirichlet values. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem annular_translated_profile_nonneg {n : ℕ} {p : ℝ}
    (hn : 1<(n:ℝ)) (hnp : (n:ℝ)<p) (hσ : 0<canonicalSphereArea n) (x : Space n) :
    0≤fundamentalPotential n (canonicalSphereArea n) p x := by
  let q : ℝ := (p-(n:ℝ))/(p-1)
  have hq : 0<q := div_pos (sub_pos.mpr hnp) (sub_pos.mpr (hn.trans hnp))
  simp only [fundamentalPotential,if_neg (ne_of_gt hnp),radialPowerPotential]
  change 0≤q⁻¹*(canonicalSphereArea n)^(-(p-1)⁻¹)*‖x‖^q
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hq.le) (Real.rpow_nonneg hσ.le _))
    (Real.rpow_nonneg (norm_nonneg _) _)

set_option maxHeartbeats 1200000 in
theorem exists_radius_threshold_annular_translated_fundamental_upper_bound
    {n : ℕ} {p : ℝ} (hn : 2≤n) (hnp : (n:ℝ)<p)
    {K : Set (Space n)} (hK : IsCompact K) {a : Space n} (ha : a∈K)
    {ε : ℝ} (hε : 0<ε) :
    ∃ T : ℝ,0<T ∧ ∀ R : ℝ,T≤R →
      ∀ (G : Space n → ℝ) (g : Space n → Space n),
        WeakPHarmonicPair p (ball 0 R\K) G g → Continuous G → (∀ x∈K,G x=0) →
        (∀ x∉ball 0 R,G x=fundamentalRadialValue n (canonicalSphereArea n) p R) →
        ∀ x∈ball 0 R,G x≤fundamentalPotential n (canonicalSphereArea n) p (x-a)+ε := by
  have hn0 : 0<n := lt_of_lt_of_le (by decide : 0<2) hn
  have hn1 : 1<n := lt_of_lt_of_le (by decide : 1<2) hn
  have hnr : 1<(n:ℝ) := by exact_mod_cast hn1
  have hσ : 0<canonicalSphereArea n := canonicalSphereArea_pos hn0
  let F : Space n → ℝ := fundamentalPotential n (canonicalSphereArea n) p
  have hF0 (x : Space n) : 0≤F x := annular_translated_profile_nonneg hnr hnp hσ x
  have hlim := tendsto_fundamentalPotential_translate_sub n (canonicalSphereArea n) hnr hnp.le a
  have he : ∀ᶠ x : Space n in Bornology.cobounded (Space n),-ε<F (x-a)-F x :=
    hlim.eventually (eventually_gt_nhds (neg_lt_zero.mpr hε))
  obtain ⟨t,_,ht⟩ := (Filter.hasBasis_cobounded_norm.eventually_iff).mp he
  refine ⟨max t 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro R hR G g hG hGc hGK hGout
  let D : Set (Space n) := ball 0 R\K
  have hD : IsOpen D := isOpen_ball.sdiff hK.isClosed
  have hDb : Bornology.IsBounded D := isBounded_ball.subset sdiff_subset
  have hDF : D⊆{x : Space n | x-a≠0} := by
    intro x hx heq
    have hxa : x=a := sub_eq_zero.mp heq
    exact hx.2 (hxa.symm ▸ ha)
  have htF := (weakPHarmonicPair_fundamentalPotential n hσ hnr hnp.le).source_zero.translate_actual (-a)
  have hFw : WeakPHarmonicPair p {x : Space n | x-a≠0}
      (fun x=>F (x-a)) (fun x=>gradient F (x-a)) := by
    simpa only [F,sub_eq_add_neg,preimage_setOf_eq] using htF.harmonic_of_source_zero
  have hFH : WeakPHarmonicPair p D (fun x=>F (x-a)+ε) (fun x=>gradient F (x-a)) :=
    (hFw.mono hDF hD).add_const ε
  have hFc : Continuous (fun x=>F (x-a)+ε) :=
    ((continuous_fundamentalPotential_supercritical n _ hnr hnp).comp
      (continuous_id.sub continuous_const)).add continuous_const
  have hboundary : ∀ y∈frontier D,G y≤F (y-a)+ε := by
    intro y hy
    by_cases hyK : y∈K
    · rw [hGK y hyK]
      exact add_nonneg (hF0 _) hε.le
    · have hyn : y∉ball (0 : Space n) R := fun hyB=>(hD.frontier_eq ▸ hy).2 ⟨hyB,hyK⟩
      have hyclosed : y∈closedBall (0 : Space n) R := closure_ball_subset_closedBall
        ((closure_mono (sdiff_subset : D⊆ball 0 R)) (frontier_subset_closure hy))
      have hynorm : ‖y‖=R := le_antisymm
        (by simpa only [mem_closedBall,dist_zero_right] using hyclosed)
        (le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hyn))
      have hyt : t≤‖y‖ := by rw [hynorm];exact (le_max_left _ _).trans hR
      have hdiff := ht hyt
      have hFy : F y=fundamentalRadialValue n (canonicalSphereArea n) p R := by
        change fundamentalPotential n (canonicalSphereArea n) p y=_
        rw [←fundamentalPotential_norm,hynorm]
      rw [hGout y hyn]
      rw [hFy] at hdiff
      linarith only [hdiff]
  have hcmp := hG.leOn_of_bounded_continuous_boundary_order hn hDb hFH
    hGc.continuousOn hFc.continuousOn hboundary
  intro x hx
  by_cases hxK : x∈K
  · rw [hGK x hxK]
    exact add_nonneg (hF0 _) hε.le
  · exact hcmp x ⟨hx,hxK⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_radius_threshold_annular_translated_fundamental_upper_bound
