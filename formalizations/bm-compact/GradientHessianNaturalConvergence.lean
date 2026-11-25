import GradientHessianNaturalMaps
import LpDominatedLimit

/-! Actual strong L2 continuity in the regularization parameter at a fixed raw
Lp gradient. The actual dominating p-energy is derived; no convergence of the
natural transform is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff RealInnerProductSpace
namespace BMCompactPDE
private theorem natural_integral_sq_norm {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal^2=∫ x,f x^2 ∂μ := by
  have he : (∫ x,f x*f x ∂μ)=inner ℝ (hf.toLp f) (hf.toLp f) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [RCLike.inner_apply,hx,starRingEnd_apply,star_trivial]
  simpa only [real_inner_self_eq_norm_sq,Lp.norm_toLp,pow_two] using he.symm

private theorem natural_weighted_square_pointwise {n : ℕ} {p : ℝ} (hp : 2≤p)
    (ε : ℝ) (v w : Space n) (z : ℝ) :
    (ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2)*‖z‖^2≤(|ε|+‖v‖+‖w‖+‖z‖)^p := by
  let H := |ε|+‖v‖+‖w‖+‖z‖
  have hH : 0≤H := by dsimp only [H];positivity
  have hM0 : 0≤max ‖v‖ ‖w‖ := (norm_nonneg _).trans (le_max_left _ _)
  have hMle : max ‖v‖ ‖w‖≤‖v‖+‖w‖ := max_le
    (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hs : Real.sqrt (ε^2+(max ‖v‖ ‖w‖)^2)≤H := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hH,?_⟩
    have hsq : ε^2+(max ‖v‖ ‖w‖)^2≤(|ε|+max ‖v‖ ‖w‖)^2 := by
      nlinarith only [mul_nonneg (abs_nonneg ε) hM0,sq_abs ε]
    exact hsq.trans ((sq_le_sq₀ (add_nonneg (abs_nonneg _) hM0) hH).mpr
      (by dsimp only [H];linarith only [hMle,norm_nonneg z]))
  have hW := Real.rpow_le_rpow (Real.sqrt_nonneg _) hs (sub_nonneg.mpr hp)
  have hweight : (Real.sqrt (ε^2+(max ‖v‖ ‖w‖)^2))^(p-2)=
      (ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (add_nonneg (sq_nonneg ε) (sq_nonneg _))]
    congr 1
    ring
  rw [hweight] at hW
  have hZ : ‖z‖^2≤H^2 := (sq_le_sq₀ (norm_nonneg _) hH).mpr
    (by dsimp only [H];linarith only [abs_nonneg ε,norm_nonneg v,norm_nonneg w])
  have hprod := mul_le_mul hW hZ (sq_nonneg _) (Real.rpow_nonneg hH _)
  have hpower : H^(p-2)*H^2=H^p := by
    by_cases hzero : H=0
    · norm_num only [hzero,Real.zero_rpow (by linarith : p≠0),mul_zero]
    · rw [←Real.rpow_two,←Real.rpow_add (lt_of_le_of_ne hH (Ne.symm hzero))]
      congr 1
      ring
  exact hprod.trans_eq hpower

private theorem natural_parameter_continuous {n : ℕ} {p : ℝ} (hp : 2≤p) (v : Space n) :
    Continuous (fun ε : ℝ => naturalGradientMap p ε v) := by
  exact (((continuous_id.pow 2).add continuous_const).rpow_const
    (fun _ => Or.inr (by linarith : 0≤(p-2)/4))).smul continuous_const

private theorem natural_sq_growth {n : ℕ} {p ε : ℝ} (hp : 2≤p) (v : Space n) :
    ‖naturalGradientMap p ε v‖^2≤(|ε|+3*‖v‖)^p := by
  rw [norm_naturalGradientMap_sq]
  have h := natural_weighted_square_pointwise hp ε v v ‖v‖
  simp only [max_self,Real.norm_eq_abs,abs_norm] at h
  have hb : |ε|+‖v‖+‖v‖+‖v‖=|ε|+3*‖v‖ := by ring
  rw [hb] at h
  exact h

theorem tendsto_eLpNorm_naturalGradientMap_parameter_sub_zero
    {n : ℕ} {p : ℝ} (hp : 2≤p) {μ : Measure (Space n)} [IsFiniteMeasure μ]
    {g : Space n → Space n} (hg : MemLp g (ENNReal.ofReal p) μ)
    {ε : ℕ → ℝ} (hεb : ∀ j,|ε j|≤1) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun x => naturalGradientMap p (ε j) (g x)-
      naturalGradientMap p 0 (g x)) 2 μ) atTop (𝓝 0) := by
  let D : ℕ → Space n → Space n := fun j x => naturalGradientMap p (ε j) (g x)-naturalGradientMap p 0 (g x)
  have hD (j : ℕ) : MemLp (D j) 2 μ :=
    (memLp_naturalGradientMap hp hg).sub (memLp_naturalGradientMap (ε:=0) hp hg)
  have hH : MemLp (fun x => 1+3*‖g x‖) (ENNReal.ofReal p) μ := by
    simpa only [Pi.add_apply] using!
      (memLp_const (1:ℝ) : MemLp (fun _ : Space n => (1:ℝ)) (ENNReal.ofReal p) μ).add (hg.norm.const_mul 3)
  have hHI : Integrable (fun x => (1+3*‖g x‖)^p) μ := by
    have hp0 : 0<p := by linarith
    have hi : Integrable (fun x => ‖1+3*‖g x‖‖^p) μ := by
      simpa only [ENNReal.toReal_ofReal hp0.le] using
        hH.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    convert hi using 1
    funext x
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤1+3*‖g x‖)]
  have hbound (j : ℕ) (x : Space n) : ‖D j x‖^2≤4*(1+3*‖g x‖)^p := by
    have hupper (e : ℝ) (he : |e|≤1) : ‖naturalGradientMap p e (g x)‖^2≤(1+3*‖g x‖)^p :=
      (natural_sq_growth hp (g x)).trans (Real.rpow_le_rpow (by positivity)
        (by linarith only [he]) (by linarith))
    have hA := hupper (ε j) (hεb j)
    have hB := hupper 0 (by norm_num)
    have hh := (sq_le_sq₀ (norm_nonneg (D j x))
      (add_nonneg (norm_nonneg (naturalGradientMap p (ε j) (g x)))
        (norm_nonneg (naturalGradientMap p 0 (g x))))).mpr
      (norm_sub_le (naturalGradientMap p (ε j) (g x)) (naturalGradientMap p 0 (g x)))
    have hsq := sq_nonneg (‖naturalGradientMap p (ε j) (g x)‖-‖naturalGradientMap p 0 (g x)‖)
    nlinarith only [hh,hA,hB,hsq]
  have hpoint (x : Space n) : Tendsto (fun j => ‖D j x‖^2) atTop (𝓝 0) := by
    have hc := ((natural_parameter_continuous hp (g x)).continuousAt.tendsto.comp hε).sub_const
      (naturalGradientMap p 0 (g x))
    simpa only [D,Function.comp_def,sub_self,norm_zero,zero_pow (by norm_num : 2≠0)] using hc.norm.pow 2
  have hInt : Tendsto (fun j => ∫ x,‖D j x‖^2 ∂μ) atTop (𝓝 (∫ x,(0:ℝ) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => 4*(1+3*‖g x‖)^p)
    · intro j
      exact (hD j).1.norm.pow 2
    · exact hHI.const_mul 4
    · intro j
      exact Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (‖D j x‖))]
        exact hbound j x)
    · exact Eventually.of_forall hpoint
  simp only [integral_zero] at hInt
  have hR : Tendsto (fun j => (eLpNorm (D j) 2 μ).toReal) atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hInt
    simp only [Real.sqrt_zero] at ht
    apply ht.congr'
    exact Eventually.of_forall (fun j => by
      have he : (eLpNorm (D j) 2 μ).toReal^2=∫ x,‖D j x‖^2 ∂μ := by
        simpa only [eLpNorm_norm] using natural_integral_sq_norm (hD j).norm
      change Real.sqrt (∫ x,‖D j x‖^2 ∂μ)=(eLpNorm (D j) 2 μ).toReal
      rw [←he,Real.sqrt_sq ENNReal.toReal_nonneg])
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hR
  simp only [ENNReal.ofReal_zero] at he
  exact he.congr' (Eventually.of_forall (fun j => ENNReal.ofReal_toReal (hD j).eLpNorm_ne_top))

end BMCompactPDE
#print axioms BMCompactPDE.tendsto_eLpNorm_naturalGradientMap_parameter_sub_zero
