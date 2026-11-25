import UpstreamGreenLocalGradientBound
import UpstreamBoundaryGreenUnique
import RootDilationBatch
import PropagationAnnular
import RadialDilation
import BallGreenOrder

/-! Uniform physical n-energy on exterior annuli at the critical exponent.
Spatial dilation, logarithmic renormalization, local Caccioppoli and the
critical Jacobian cancellation give one energy bound at every large scale. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Bornology
open scoped Topology ENNReal
namespace BMCompactPDE

theorem WeakPHarmonicPair.uniform_critical_green_annular_energy
    {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0 < σ) {K : Set (Space n)} (hK : IsCompact K)
    {u : Space n → ℝ} {g : Space n → Space n} (hg : WeakPHarmonicPair (n : ℝ) Kᶜ u g)
    (hrem : HasBoundedGreenRemainder n σ n u) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ R : ℝ in atTop,
      (∫ y in radialAnnulusAt n 0 (2*R) (4*R), ‖g y‖^n ∂volume) ≤ E := by
  have hp : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  let U := radialAnnulusAt n 0 1 5
  let D := radialAnnulusAt n 0 2 4
  have hU : IsOpen U := isOpen_radialAnnulusAt _ _ _ _
  have hD : LocalDomain D U := by
    refine ⟨isOpen_radialAnnulusAt _ _ _ _,isBounded_radialAnnulusAt _ _ _ _,?_⟩
    intro x hx
    have hb := bounds_of_mem_closure_radialAnnulusAt n 0 2 4 hx
    exact ⟨(by norm_num : (1:ℝ)<2).trans_le hb.1,hb.2.trans_lt (by norm_num)⟩
  obtain ⟨C,hC,hest⟩ := exists_local_gradient_norm_bound_of_scalar_bound hp hU hD
  obtain ⟨A,hA,hAb⟩ := hrem
  obtain ⟨t,_,ht⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hAb
  obtain ⟨s,hs,hKs⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space n)
  let f := fundamentalRadialValue n σ (n : ℝ)
  let B := A + |f 1| + |f 5|
  have hB : 0 ≤ B := add_nonneg (add_nonneg hA (abs_nonneg _)) (abs_nonneg _)
  refine ⟨(C*B)^n,pow_nonneg (mul_nonneg hC hB) _,?_⟩
  filter_upwards [eventually_gt_atTop (max t s)] with R hR
  have hRpos : 0 < R := hs.trans ((le_max_right _ _).trans_lt hR)
  let c := σ ^ (-((n:ℝ)-1)⁻¹) * Real.log R
  have hxn (x : Space n) (hx : x ∈ U) : 1 < ‖x‖ ∧ ‖x‖ < 5 := by
    simpa only [U,radialAnnulusAt,mem_ofPred_eq,dist_zero_right] using hx
  have hRnorm (x : Space n) (hx : x ∈ U) : R < ‖R • x‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hRpos]
    simpa only [mul_one] using mul_lt_mul_of_pos_left (hxn x hx).1 hRpos
  have hdomain : U ⊆ (fun x : Space n => R • x) ⁻¹' Kᶜ := by
    intro x hx hbad
    have hsmall : ‖R • x‖ < s := by simpa only [mem_ball,dist_zero_right] using hKs hbad
    exact (not_lt_of_ge ((le_max_right t s).trans (hR.trans (hRnorm x hx)).le)) hsmall
  have hscaled := hg.source_zero.dilation_actual hRpos
  rw [mul_zero] at hscaled
  have hlocal := (hscaled.harmonic_of_source_zero.mono hdomain hU).add_const (-c)
  have hbound (x : Space n) (hx : x ∈ U) : |u (R • x)+(-c)| ≤ B := by
    have hremx := ht (show R • x ∈ {y : Space n | t ≤ ‖y‖} from
      (le_max_left _ _).trans (hR.trans (hRnorm x hx)).le)
    have hx' := hxn x hx
    have hpos : 0 < ‖x‖ := zero_lt_one.trans hx'.1
    have heq := fundamentalPotential_dilate_critical n σ hRpos (norm_pos_iff.mp hpos)
    have h1 := fundamentalRadialValue_mono_positive n hp le_rfl hσ zero_lt_one hx'.1.le
    have h5 := fundamentalRadialValue_mono_positive n hp le_rfl hσ hpos hx'.2.le
    rw [fundamentalPotential_norm] at h1 h5
    change fundamentalPotential n σ (n:ℝ) (R • x)=fundamentalPotential n σ (n:ℝ) x+c at heq
    change f 1 ≤ fundamentalPotential n σ (n:ℝ) x at h1
    change fundamentalPotential n σ (n:ℝ) x ≤ f 5 at h5
    apply abs_le.mpr
    dsimp only [B]
    constructor <;> linarith only [(abs_le.mp hremx).1,(abs_le.mp hremx).2,heq,h1,h5,
      neg_le_abs (f 1),le_abs_self (f 5),abs_nonneg (f 1),abs_nonneg (f 5)]
  let G := fun x : Space n => R • g (R • x)
  have hgn := hest _ G hlocal B hB hbound
  have hmem : MemLp G (ENNReal.ofReal (n : ℝ)) (volume.restrict D) := (hlocal.2.2.1 D hD).2.2.1
  let : Fact (1 ≤ ENNReal.ofReal (n : ℝ)) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have he := BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp) (hmem.toLp G)
  rw [Lp.norm_toLp] at he
  have hae := integral_congr_ae (hmem.coeFn_toLp.fun_comp (fun v => ‖v‖^(n : ℝ)))
  have henergy : (∫ x in D, ‖G x‖^n) ≤ (C*B)^n := by
    have hid := (he.trans hae).symm
    simp only [Real.rpow_natCast] at hid
    exact hid.le.trans (pow_le_pow_left₀ ENNReal.toReal_nonneg hgn _)
  let V := radialAnnulusAt n 0 (2*R) (4*R)
  have hpre : (fun x : Space n => R • x) ⁻¹' V = D := by
    ext x
    simp only [D,V,radialAnnulusAt,mem_preimage,mem_ofPred_eq,dist_zero_right,
      norm_smul,Real.norm_eq_abs,abs_of_pos hRpos,mul_comm (2:ℝ) R,mul_comm (4:ℝ) R,
      mul_lt_mul_iff_right₀ hRpos]
  have hchange := integral_comp_dilation_restrict (isOpen_radialAnnulusAt n 0 (2*R) (4*R)).measurableSet
    hRpos.ne' (fun y => ‖g y‖^n)
  change (∫ x in (fun x : Space n => R • x) ⁻¹' V, ‖g (R • x)‖^n) =
    |(R^n)⁻¹| * ∫ y in V, ‖g y‖^n at hchange
  rw [hpre,abs_of_pos (inv_pos.mpr (pow_pos hRpos n))] at hchange
  have heq : (∫ x in D, ‖G x‖^n) = ∫ y in V, ‖g y‖^n := by
    simp only [G,norm_smul,Real.norm_eq_abs,abs_of_pos hRpos,mul_pow,integral_const_mul,hchange,
      ←mul_assoc,mul_inv_cancel₀ (pow_ne_zero n hRpos.ne'),one_mul]
  exact heq ▸ henergy

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.uniform_critical_green_annular_energy
