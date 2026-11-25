import CriticalGreenAnnularEnergy
import Mathlib.Analysis.Calculus.BumpFunction.Basic

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ContDiff
namespace BMCompactPDE

/-- Smooth spatial cutoffs with gradient confined strictly to the open shell
and one n-energy independent of the physical radius. -/
theorem exists_critical_shell_cutoffs (n : ℕ) (hn : 0<n) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ R : ℝ, 0<R → ∃ η : Space n → ℝ,
      ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 2*R → η x=1) ∧ (∀ x, 4*R ≤ ‖x‖ → η x=0) ∧
      (∀ x, x ∉ radialAnnulusAt n 0 (2*R) (4*R) → gradient η x=0) ∧
      Integrable (fun x => ‖gradient η x‖^n) volume ∧
      (∫ x, ‖gradient η x‖^n ∂volume) = P := by
  let β : ContDiffBump (0 : Space n) := ⟨5/2,7/2,by norm_num,by norm_num⟩
  let b := (β : Space n → ℝ)
  have hb : ContDiff ℝ ∞ b := β.contDiff
  refine ⟨∫ x, ‖gradient b x‖^n ∂volume,integral_nonneg (fun _=>pow_nonneg (norm_nonneg _) n),?_⟩
  intro R hR
  let η := fun x : Space n => b (R⁻¹ • x)
  have hη : ContDiff ℝ ∞ η := hb.comp (by fun_prop : ContDiff ℝ ∞ (fun x : Space n => R⁻¹ • x))
  have hnorm (x : Space n) : ‖R⁻¹ • x‖ = R⁻¹ * ‖x‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
  have hone (x : Space n) (hx : ‖x‖ < (5/2)*R) : η x=1 := by
    apply β.one_of_mem_closedBall
    change dist (R⁻¹ • x) 0 ≤ 5/2
    rw [dist_zero_right,hnorm,← div_eq_inv_mul]
    exact (div_le_iff₀ hR).mpr hx.le
  have hoff (x : Space n) (hx : (7/2)*R < ‖x‖) : η x=0 := by
    apply β.zero_of_le_dist
    change 7/2 ≤ dist (R⁻¹ • x) 0
    rw [dist_zero_right,hnorm,←div_eq_inv_mul]
    exact (le_div_iff₀ hR).mpr hx.le
  have hs : tsupport η ⊆ closedBall 0 ((7/2)*R) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hnot
    exact hx (hoff x (lt_of_not_ge (by simpa only [mem_closedBall,dist_zero_right] using hnot)))
  have hcomp : HasCompactSupport η :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hs
  have hgcont := BMCompactCapacityV2.continuous_gradient_of_contDiff hη
  have hgcomp := BMCompactCapacityV2.gradient_hasCompactSupport hcomp
  have hsupp : Function.support (fun x => ‖gradient η x‖^n) ⊆ tsupport (gradient η) := by
    intro x hx
    by_contra hnot
    apply hx
    change ‖gradient η x‖^n = 0
    rw [image_eq_zero_of_notMem_tsupport hnot,norm_zero,zero_pow (Nat.ne_of_gt hn)]
  have hI : Integrable (fun x => ‖gradient η x‖^n) volume :=
    (hgcont.norm.pow n).integrable_of_hasCompactSupport
      (hgcomp.of_isClosed_subset (isClosed_tsupport _) (closure_minimal hsupp (isClosed_tsupport _)))
  refine ⟨η,hη,hcomp,fun _=>⟨β.nonneg,β.le_one⟩,
    fun x hx => hone x (by linarith only [hx,hR]),fun x hx => hoff x (by linarith only [hx,hR]),?_,hI,?_⟩
  · intro x hx
    by_cases hin : ‖x‖ ≤ 2*R
    · have he : η =ᶠ[𝓝 x] (fun _ => (1:ℝ)) := by
        filter_upwards [continuous_norm.continuousAt.eventually (eventually_lt_nhds
          (show ‖x‖ < (5/2)*R by linarith only [hin,hR]))] with y hy
        exact hone y hy
      simp only [gradient,he.fderiv_eq,fderiv_const_apply, map_zero]
    · have hout : 4*R ≤ ‖x‖ := by
        by_contra! h
        exact hx (by simpa only [radialAnnulusAt,mem_ofPred_eq,dist_zero_right] using
          (And.intro (lt_of_not_ge hin) h))
      apply BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
      intro hxt
      have hh : ‖x‖ ≤ (7/2)*R := by simpa only [mem_closedBall,dist_zero_right] using hs hxt
      linarith only [hh,hout,hR]
  · have hg (x : Space n) : ‖gradient η x‖=R⁻¹*‖gradient b (R⁻¹ • x)‖ := by
      simp only [gradient,LinearIsometryEquiv.norm_map,η,fderiv_comp_smul,norm_smul,
        Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    have hchange := integral_comp_dilation_restrict (n:=n) MeasurableSet.univ (inv_ne_zero hR.ne')
      (fun x=>‖gradient b x‖^n)
    simp only [preimage_univ,Measure.restrict_univ,inv_pow,inv_inv,abs_of_pos (pow_pos hR n)] at hchange
    simp only [hg,mul_pow,integral_const_mul,hchange,inv_pow,←mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero n hR.ne'),one_mul]

end BMCompactPDE
#print axioms BMCompactPDE.exists_critical_shell_cutoffs
