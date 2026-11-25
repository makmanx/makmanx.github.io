import GradientRegularizedConstruction

/-! Weighted quadratic monotonicity for p>=2, including the actual regularized
operator. This is stronger for difference-quotient estimates than the p-power
Clarkson bound: the coefficient retains the size of the underlying gradients.
No property of a weak solution or a desired energy bound is assumed. -/
noncomputable section
set_option autoImplicit false
open Set InnerProductSpace
namespace BMCompactPDE

private theorem gradient_weighted_coercivity_ordered
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p : ℝ} (hp : 2≤p) (v w : E) (hvw : ‖v‖≤‖w‖) :
    (1/2 : ℝ)*‖w‖^(p-2)*‖v-w‖^2 ≤ inner ℝ (pFlux p v-pFlux p w) (v-w) := by
  have hp1 : 1<p := lt_of_lt_of_le (by norm_num : (1 : ℝ)<2) hp
  let r := ‖v‖
  let s := ‖w‖
  let z := inner ℝ v w
  let A := r^(p-2)
  let B := s^(p-2)
  have hr : 0≤r := norm_nonneg _
  have hs : 0≤s := norm_nonneg _
  have hA : 0≤A := Real.rpow_nonneg hr _
  have hB : 0≤B := Real.rpow_nonneg hs _
  have hAB : A≤B := Real.rpow_le_rpow hr hvw (sub_nonneg.mpr hp)
  have hT : 0≤r*s-z := sub_nonneg.mpr (real_inner_le_norm v w)
  have hrpow := rpow_coefficient_mul hp1 hr
  have hspow := rpow_coefficient_mul hp1 hs
  have hrad : B*(r-s)^2≤(r^(p-1)-s^(p-1))*(r-s) := by
    rw [← hrpow,← hspow]
    have hh := mul_nonneg (mul_nonneg (sub_nonneg.mpr hAB) hr)
      (sub_nonneg.mpr hvw)
    change 0≤(B-A)*r*(s-r) at hh
    dsimp only [A,B] at hh ⊢
    nlinarith only [hh]
  have hD : inner ℝ (pFlux p v-pFlux p w) (v-w)=
      (r^(p-1)-s^(p-1))*(r-s)+(A+B)*(r*s-z) := by
    dsimp only [A,B,r,s,z] at *
    simp only [pFlux,inner_sub_left,inner_sub_right,real_inner_smul_left,
      real_inner_self_eq_norm_mul_norm,real_inner_comm w v]
    rw [← hrpow,← hspow]
    ring
  have hnorm : ‖v-w‖^2=(r-s)^2+2*(r*s-z) := by
    rw [norm_sub_sq_real]
    dsimp only [r,s,z]
    ring
  have hang := mul_nonneg hA hT
  have hsq := mul_nonneg hB (sq_nonneg (r-s))
  rw [hD,hnorm]
  change (1/2 : ℝ)*B*((r-s)^2+2*(r*s-z))≤_
  nlinarith only [hrad,hang,hsq]

theorem pFlux_pairing_controls_weighted_difference_ge_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p : ℝ} (hp : 2≤p) (v w : E) :
    (1/2 : ℝ)*(max ‖v‖ ‖w‖)^(p-2)*‖v-w‖^2≤
      inner ℝ (pFlux p v-pFlux p w) (v-w) := by
  rcases le_total ‖v‖ ‖w‖ with hvw|hwv
  · rw [max_eq_right hvw]
    exact gradient_weighted_coercivity_ordered hp v w hvw
  · have hh := gradient_weighted_coercivity_ordered hp w v hwv
    rw [max_eq_left hwv]
    have hD : inner ℝ (pFlux p w-pFlux p v) (w-v)=
        inner ℝ (pFlux p v-pFlux p w) (v-w) := by
      rw [← inner_neg_neg]
      simp only [neg_sub]
    simpa only [norm_sub_rev,hD] using hh

theorem regularized_pFlux_weighted_monotonicity_ge_two
    {n : ℕ} {p : ℝ} (hp : 2≤p) (ε : ℝ) (v w : Space n) :
    (1/2 : ℝ)*(max (Real.sqrt (ε^2+‖v‖^2)) (Real.sqrt (ε^2+‖w‖^2)))^(p-2)*‖v-w‖^2≤
      inner ℝ
        ((ε^2+‖v‖^2)^((p-2)/2) • v-(ε^2+‖w‖^2)^((p-2)/2) • w) (v-w) := by
  let V : GradientAugmentedSpace n := WithLp.toLp 2 (ε,v)
  let W : GradientAugmentedSpace n := WithLp.toLp 2 (ε,w)
  have hsub : V-W=gradientAugmentedInjection n (v-w) := by
    rw [gradientAugmentedInjection_apply]
    change WithLp.toLp 2 (ε,v)-WithLp.toLp 2 (ε,w)=_
    rw [← WithLp.toLp_sub]
    congr 1
    ext <;> simp
  have hnorm : ‖V-W‖=‖v-w‖ := by rw [hsub,gradientAugmentedInjection_norm]
  have hpair : inner ℝ (pFlux p V-pFlux p W) (V-W)=
      inner ℝ
        ((ε^2+‖v‖^2)^((p-2)/2) • v-(ε^2+‖w‖^2)^((p-2)/2) • w) (v-w) := by
    rw [hsub,inner_sub_left,gradientAugmentedFlux_pairing,
      gradientAugmentedFlux_pairing,← inner_sub_left]
  have hv : ‖V‖=Real.sqrt (ε^2+‖v‖^2) := by
    rw [WithLp.prod_norm_eq_of_L2]
    simp only [V,WithLp.toLp_fst,WithLp.toLp_snd,Prod.fst,Prod.snd,
      Real.norm_eq_abs,sq_abs]
  have hw : ‖W‖=Real.sqrt (ε^2+‖w‖^2) := by
    rw [WithLp.prod_norm_eq_of_L2]
    simp only [W,WithLp.toLp_fst,WithLp.toLp_snd,Prod.fst,Prod.snd,
      Real.norm_eq_abs,sq_abs]
  have hh := pFlux_pairing_controls_weighted_difference_ge_two hp V W
  rw [hnorm,hpair,hv,hw] at hh
  exact hh

theorem regularized_pFlux_weighted_monotonicity_le_two
    {n : ℕ} {p : ℝ} (hp : 1<p) (hp2 : p≤2) (ε : ℝ) (v w : Space n) :
    (p-1)*(Real.sqrt (ε^2+‖v‖^2)+Real.sqrt (ε^2+‖w‖^2))^(p-2)*‖v-w‖^2≤
      inner ℝ
        ((ε^2+‖v‖^2)^((p-2)/2) • v-(ε^2+‖w‖^2)^((p-2)/2) • w) (v-w) := by
  let V : GradientAugmentedSpace n := WithLp.toLp 2 (ε,v)
  let W : GradientAugmentedSpace n := WithLp.toLp 2 (ε,w)
  have hsub : V-W=gradientAugmentedInjection n (v-w) := by
    rw [gradientAugmentedInjection_apply]
    change WithLp.toLp 2 (ε,v)-WithLp.toLp 2 (ε,w)=_
    rw [← WithLp.toLp_sub]
    congr 1
    ext <;> simp
  have hnorm : ‖V-W‖=‖v-w‖ := by rw [hsub,gradientAugmentedInjection_norm]
  have hpair : inner ℝ (pFlux p V-pFlux p W) (V-W)=
      inner ℝ
        ((ε^2+‖v‖^2)^((p-2)/2) • v-(ε^2+‖w‖^2)^((p-2)/2) • w) (v-w) := by
    rw [hsub,inner_sub_left,gradientAugmentedFlux_pairing,
      gradientAugmentedFlux_pairing,← inner_sub_left]
  have hv : ‖V‖=Real.sqrt (ε^2+‖v‖^2) := by
    rw [WithLp.prod_norm_eq_of_L2]
    simp only [V,WithLp.toLp_fst,WithLp.toLp_snd,Prod.fst,Prod.snd,
      Real.norm_eq_abs,sq_abs]
  have hw : ‖W‖=Real.sqrt (ε^2+‖w‖^2) := by
    rw [WithLp.prod_norm_eq_of_L2]
    simp only [W,WithLp.toLp_fst,WithLp.toLp_snd,Prod.fst,Prod.snd,
      Real.norm_eq_abs,sq_abs]
  have hh := pFlux_pairing_controls_weighted_difference hp hp2 V W
  rw [hnorm,hpair,hv,hw] at hh
  exact hh

theorem regularized_pFlux_jacobian_norm_le_ge_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p ε : ℝ} (hp : 2≤p) (hε : ε≠0) (v : E) :
    ‖fderiv ℝ (fun w : E => (ε^2+‖w‖^2)^((p-2)/2) • w) v‖≤
      (p-1)*(ε^2+‖v‖^2)^((p-2)/2) := by
  let S := ε^2+‖v‖^2
  let A := S^((p-2)/2)
  let B := (p-2)*S^((p-4)/2)
  have hS : 0<S := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hε) (sq_nonneg _)
  have hA : 0≤A := Real.rpow_nonneg hS.le _
  have hB : 0≤B := mul_nonneg (sub_nonneg.mpr hp) (Real.rpow_nonneg hS.le _)
  have hshift : S^((p-4)/2)*S=A := by
    change S^((p-4)/2)*S=S^((p-2)/2)
    rw [← Real.rpow_add_one hS.ne']
    congr 1
    ring
  have hcoef : B*‖v‖^2≤(p-2)*A := by
    calc
      B*‖v‖^2≤B*S := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (sq_nonneg ε)) hB
      _=(p-2)*A := by dsimp only [B];rw [mul_assoc,hshift]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by linarith) hA)
  intro h
  rw [(hasFDerivAt_regularized_pFlux p hε v).fderiv]
  change ‖A • h+(B*inner ℝ v h) • v‖≤(p-1)*A*‖h‖
  have hsecond : ‖(B*inner ℝ v h) • v‖≤(B*‖v‖^2)*‖h‖ := by
    calc
      ‖(B*inner ℝ v h) • v‖=B*|inner ℝ v h| * ‖v‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hB]
      _≤B*(‖v‖*‖h‖)*‖v‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm v h) hB) (norm_nonneg v)
      _=(B*‖v‖^2)*‖h‖ := by ring
  calc
    _≤‖A • h‖+‖(B*inner ℝ v h) • v‖ := norm_add_le _ _
    _≤A*‖h‖+(B*‖v‖^2)*‖h‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hA]
      exact add_le_add le_rfl hsecond
    _≤A*‖h‖+((p-2)*A)*‖h‖ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hcoef (norm_nonneg h))
    _=(p-1)*A*‖h‖ := by ring

theorem regularized_pFlux_difference_norm_le_ge_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p ε : ℝ} (hp : 2≤p) (hε : ε≠0) (v w : E) :
    ‖(ε^2+‖v‖^2)^((p-2)/2) • v-(ε^2+‖w‖^2)^((p-2)/2) • w‖≤
      (p-1)*(ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2)*‖v-w‖ := by
  let M := max ‖v‖ ‖w‖
  have hM : 0≤M := (norm_nonneg v).trans (le_max_left _ _)
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := Metric.closedBall (0 : E) M)
    (fun x _ => (hasFDerivAt_regularized_pFlux p hε x).differentiableAt)
    (fun x hx => ?_) (convex_closedBall (0 : E) M)
    (by simpa only [Metric.mem_closedBall,dist_zero_right,M] using le_max_right ‖v‖ ‖w‖)
    (by simpa only [Metric.mem_closedBall,dist_zero_right,M] using le_max_left ‖v‖ ‖w‖)
  have hxM : ‖x‖≤M := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  apply (regularized_pFlux_jacobian_norm_le_ge_two hp hε x).trans
  apply mul_le_mul_of_nonneg_left _ (by linarith : 0≤p-1)
  apply Real.rpow_le_rpow (add_nonneg (sq_nonneg ε) (sq_nonneg _)) _ (by linarith)
  exact add_le_add le_rfl ((sq_le_sq₀ (norm_nonneg x) hM).mpr hxM)

end BMCompactPDE
#print axioms BMCompactPDE.pFlux_pairing_controls_weighted_difference_ge_two
#print axioms BMCompactPDE.regularized_pFlux_weighted_monotonicity_ge_two
#print axioms BMCompactPDE.regularized_pFlux_weighted_monotonicity_le_two
#print axioms BMCompactPDE.regularized_pFlux_jacobian_norm_le_ge_two
#print axioms BMCompactPDE.regularized_pFlux_difference_norm_le_ge_two
