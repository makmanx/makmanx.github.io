import GradientRegularizedDifference

/-! Genuine regularized quadratic finite-difference energy, p>=2. Weighted
integrability comes from the actual Lp fields, and the W0 difference test is
constructed from a compact smooth multiplier. No Hessian or gradient bound
or desired energy estimate is an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

private theorem gradient_weight_sqrt (p ε M : ℝ) :
    (ε^2+M^2)^((p-2)/2)=(Real.sqrt (ε^2+M^2))^(p-2) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul (add_nonneg (sq_nonneg ε) (sq_nonneg M))]
  congr 1
  ring

private theorem gradient_regularized_max_weight_eq {n : ℕ} (p ε : ℝ) (v w : Space n) :
    (max (Real.sqrt (ε^2+‖v‖^2)) (Real.sqrt (ε^2+‖w‖^2)))^(p-2)=
      (ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2) := by
  rcases le_total ‖v‖ ‖w‖ with hvw|hwv
  · have hs := Real.sqrt_le_sqrt (add_le_add (show ε^2≤ε^2 from le_rfl)
      ((sq_le_sq₀ (norm_nonneg v) (norm_nonneg w)).mpr hvw))
    rw [max_eq_right hs,max_eq_right hvw]
    exact (gradient_weight_sqrt p ε ‖w‖).symm
  · have hs := Real.sqrt_le_sqrt (add_le_add (show ε^2≤ε^2 from le_rfl)
      ((sq_le_sq₀ (norm_nonneg w) (norm_nonneg v)).mpr hwv))
    rw [max_eq_left hs,max_eq_left hwv]
    exact (gradient_weight_sqrt p ε ‖v‖).symm

theorem integrable_regularized_weighted_square {n : ℕ} {p ε : ℝ} (hp : 2≤p)
    {μ : Measure (Space n)} [IsFiniteMeasure μ]
    {g h : Space n → Space n} {z : Space n → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) μ) (hh : MemLp h (ENNReal.ofReal p) μ)
    (hz : MemLp z (ENNReal.ofReal p) μ) :
    Integrable (fun x => (ε^2+(max ‖g x‖ ‖h x‖)^2)^((p-2)/2)*‖z x‖^2) μ := by
  have hp0 : 0<p := lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) hp
  let H : Space n → ℝ := fun x => |ε|+‖g x‖+‖h x‖+‖z x‖
  have hH0 (x : Space n) : 0≤H x := by dsimp only [H];positivity
  have hHM : MemLp H (ENNReal.ofReal p) μ := by
    convert! (((memLp_const |ε|).add hg.norm).add hh.norm).add hz.norm using 1
  have hHI : Integrable (fun x => (H x)^p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le,Real.norm_eq_abs,abs_of_nonneg (hH0 _)] using
      hHM.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  have hweight : AEMeasurable (fun x => (ε^2+(max ‖g x‖ ‖h x‖)^2)^((p-2)/2)) μ :=
    (aemeasurable_const.add ((hg.1.norm.aemeasurable.max hh.1.norm.aemeasurable).pow_const
      (2 : ℕ))).pow_const _
  have hm : AEStronglyMeasurable
      (fun x => (ε^2+(max ‖g x‖ ‖h x‖)^2)^((p-2)/2)*‖z x‖^2) μ :=
    (hweight.mul (hz.1.norm.aemeasurable.pow_const (2 : ℕ))).aestronglyMeasurable
  apply hHI.mono' hm
  apply Eventually.of_forall
  intro x
  have hM0 : 0≤max ‖g x‖ ‖h x‖ := (norm_nonneg _).trans (le_max_left _ _)
  have hMle : max ‖g x‖ ‖h x‖≤‖g x‖+‖h x‖ := max_le
    (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hs : Real.sqrt (ε^2+(max ‖g x‖ ‖h x‖)^2)≤H x := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hH0 x,?_⟩
    have hsq : ε^2+(max ‖g x‖ ‖h x‖)^2≤(|ε|+max ‖g x‖ ‖h x‖)^2 := by
      nlinarith only [mul_nonneg (abs_nonneg ε) hM0,sq_abs ε]
    exact hsq.trans ((sq_le_sq₀ (add_nonneg (abs_nonneg _) hM0) (hH0 x)).mpr
      (by dsimp only [H];linarith only [hMle,norm_nonneg (z x)]))
  have hW := Real.rpow_le_rpow (Real.sqrt_nonneg _) hs (sub_nonneg.mpr hp)
  rw [←gradient_weight_sqrt] at hW
  have hZ : ‖z x‖^2≤(H x)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (hH0 x)).mpr (by
      dsimp only [H]
      linarith only [abs_nonneg ε,norm_nonneg (g x),norm_nonneg (h x)])
  have hprod := mul_le_mul hW hZ (sq_nonneg _) (Real.rpow_nonneg (hH0 x) _)
  have hpower : (H x)^(p-2)*(H x)^2=(H x)^p := by
    by_cases hzero : H x=0
    · norm_num only [hzero,Real.zero_rpow hp0.ne',mul_zero]
    · have hpos : 0<H x := lt_of_le_of_ne (hH0 x) (Ne.symm hzero)
      rw [←Real.rpow_two,←Real.rpow_add hpos]
      congr 1
      ring
  rw [hpower] at hprod
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) _) (sq_nonneg _))]
  exact hprod

private theorem gradient_regularized_cutoff_error_bound {n : ℕ} {p ε η z : ℝ}
    (hp : 2≤p) (hε : ε≠0) (hη : 0≤η) (v w b : Space n) :
    -z*inner ℝ
      ((ε^2+‖v‖^2)^((p-2)/2) • v-(ε^2+‖w‖^2)^((p-2)/2) • w) ((2*η) • b) ≤
      (1/4 : ℝ)*η^2*(ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2)*‖v-w‖^2+
        4*(p-1)^2*(ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2)*z^2*‖b‖^2 := by
  let W := (ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2)
  let F := (ε^2+‖v‖^2)^((p-2)/2) • v-(ε^2+‖w‖^2)^((p-2)/2) • w
  have hW : 0≤W := Real.rpow_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) _
  have hF : ‖F‖≤(p-1)*W*‖v-w‖ := regularized_pFlux_difference_norm_le_ge_two hp hε v w
  have hraw : -z*inner ℝ F ((2*η) • b)≤2*|z| *η*((p-1)*W*‖v-w‖)*‖b‖ := by
    calc
      _=-(z*inner ℝ F ((2*η) • b)) := by ring
      _≤|z*inner ℝ F ((2*η) • b)| := neg_le_abs _
      _=|z| * |inner ℝ F ((2*η) • b)| := abs_mul _ _
      _≤|z| * (‖F‖*‖(2*η) • b‖) := mul_le_mul_of_nonneg_left
        (abs_real_inner_le_norm _ _) (abs_nonneg _)
      _=2*|z| *η*‖F‖*‖b‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by norm_num) hη)]
        ring
      _≤_ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hF (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) hη))
        (norm_nonneg _)
  have hYoung : 2*(p-1)*(η*‖v-w‖)*(|z| * ‖b‖)≤
      (1/4 : ℝ)*η^2*‖v-w‖^2+4*(p-1)^2*z^2*‖b‖^2 := by
    rw [←sq_abs z]
    nlinarith only [sq_nonneg (η*‖v-w‖/2-2*(p-1)*|z| * ‖b‖)]
  have hweighted := mul_le_mul_of_nonneg_left hYoung hW
  exact hraw.trans (by dsimp only [W] at *;nlinarith only [hweighted])

set_option maxHeartbeats 1600000 in
theorem GlobalWeakRegularizedSourcePair.caccioppoli_difference_ge_two
    {n : ℕ} {p ε c : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g)
    (hv : GlobalWeakRegularizedSourcePair p ε c Ω v h)
    (hp : 2≤p) (hε : ε≠0) (hΩb : Bornology.IsBounded Ω)
    {η : Space n → ℝ} (hη : SmoothTest Ω η) (hη0 : ∀ x,0≤η x) :
    (∫ x in Ω,η x^2*(ε^2+(max ‖g x‖ ‖h x‖)^2)^((p-2)/2)*‖g x-h x‖^2)≤
      16*(p-1)^2*∫ x in Ω,(ε^2+(max ‖g x‖ ‖h x‖)^2)^((p-2)/2)*
        |u x-v x|^2*‖gradient η x‖^2 := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  let W : Space n → ℝ := fun x => (ε^2+(max ‖g x‖ ‖h x‖)^2)^((p-2)/2)
  let L : Space n → ℝ := fun x => η x^2*W x*‖g x-h x‖^2
  let R : Space n → ℝ := fun x => W x*|u x-v x|^2*‖gradient η x‖^2
  let χ : Space n → ℝ := fun x => η x*η x
  have hχ : SmoothTest Ω χ :=
    ⟨hη.1.mul hη.1,hη.2.1.mul_right,tsupport_mul_subset_left.trans hη.2.2⟩
  have hgrad (x : Space n) : gradient χ x=(2*η x) • gradient η x := by
    rw [gradient_fun_mul_actual (hη.1.differentiable (by simp)).differentiableAt
      (hη.1.differentiable (by simp)).differentiableAt]
    module
  have hbase : Integrable (fun x => W x*‖u x-v x‖^2) (volume.restrict Ω) :=
    integrable_regularized_weighted_square hp hu.2.2.1.2.2.1 hv.2.2.1.2.2.1
      (hu.2.2.1.2.1.sub hv.2.2.1.2.1)
  have hgradtop : MemLp (gradient η) (∞ : ℝ≥0∞) (volume.restrict Ω) :=
    (continuous_gradient_of_contDiff_one (hη.1.of_le (by simp))).memLp_top_of_hasCompactSupport
      (BMCompactCapacityV2.gradient_hasCompactSupport hη.2.1) _
  have hgradpow : MemLp (fun x => ‖gradient η x‖^2) (∞ : ℝ≥0∞) (volume.restrict Ω) := by
    simpa only [pow_two] using hgradtop.norm.mul' hgradtop.norm
  have hRI : Integrable R (volume.restrict Ω) := by
    simpa only [R,Pi.mul_apply,Real.norm_eq_abs,Pi.sub_apply,mul_comm] using!
      hbase.mul_of_top_right hgradpow
  have hLI : Integrable L (volume.restrict Ω) := by
    have hb := integrable_regularized_weighted_square (ε := ε) hp hu.2.2.1.2.2.1 hv.2.2.1.2.2.1
      (hu.2.2.1.2.2.1.sub hv.2.2.1.2.2.1).norm
    have hηtop := hη.1.continuous.memLp_top_of_hasCompactSupport hη.2.1 (volume.restrict Ω)
    have hηpow : MemLp (fun x => η x^2) (∞ : ℝ≥0∞) (volume.restrict Ω) := by
      simpa only [pow_two] using hηtop.mul' hηtop
    have hi := hb.mul_of_top_right hηpow
    convert! hi using 1
    funext x
    simp only [L,Pi.mul_apply,Real.norm_eq_abs,Pi.sub_apply,abs_norm]
    ring
  obtain ⟨hA,hB,he⟩ := hu.local_flux_difference_identity hv hΩb hχ
  have hco := integral_mono (hLI.const_mul (1/2 : ℝ)) hA (fun x => by
    have hh := regularized_pFlux_weighted_monotonicity_ge_two hp ε (g x) (h x)
    rw [gradient_regularized_max_weight_eq] at hh
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg (η x))
    simpa only [L,χ,W,pow_two,mul_assoc,mul_left_comm,mul_comm] using hm)
  rw [integral_const_mul] at hco
  have hYoung := integral_mono hB.neg
    ((hLI.const_mul (1/4 : ℝ)).add (hRI.const_mul (4*(p-1)^2))) (fun x => by
      have hh := gradient_regularized_cutoff_error_bound hp hε (hη0 x) (g x) (h x) (gradient η x)
        (z := u x-v x)
      simp only [Pi.neg_apply,Pi.add_apply]
      rw [hgrad] 
      simpa only [L,R,W,Pi.add_apply,neg_mul,mul_assoc,sq_abs] using hh)
  change (∫ x in Ω,-((u x-v x)*inner ℝ
    ((ε^2+‖g x‖^2)^((p-2)/2) • g x-(ε^2+‖h x‖^2)^((p-2)/2) • h x) (gradient χ x)))≤
      ∫ x in Ω,(1/4 : ℝ)*L x+(4*(p-1)^2)*R x at hYoung
  rw [integral_neg,integral_add (hLI.const_mul (1/4 : ℝ)) (hRI.const_mul (4*(p-1)^2)),
    integral_const_mul,integral_const_mul] at hYoung
  change (∫ x in Ω,L x)≤16*(p-1)^2*∫ x in Ω,R x
  nlinarith only [hco,hYoung,he]

end BMCompactPDE
#print axioms BMCompactPDE.integrable_regularized_weighted_square
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.caccioppoli_difference_ge_two
