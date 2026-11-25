import GradientHessianNaturalConvergence
import CapacityNaturalHolderRegularized

/-! Strong Lp data and a vanishing regularization parameter give actual strong
L2 convergence of the natural gradient. The quantitative Holder estimate keeps
the small Lp difference factor; no Nemytskii continuity is assumed. -/
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

private theorem natural_uniform_norm_of_strong_corrections
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {P : ℝ≥0∞} (hP : 1≤P)
    {f : α → F} {w : ℕ → α → F} (hf : MemLp f P μ) (hw : ∀ j,MemLp (w j) P μ)
    (hlim : Tendsto (fun j => eLpNorm (w j) P μ) atTop (𝓝 0)) :
    ∃ N : ℝ,0≤N ∧ ∀ j,(eLpNorm (f+w j) P μ).toReal≤N := by
  have ht : Tendsto (fun j => (eLpNorm (w j) P μ).toReal) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero,Function.comp_def] using
      (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞)≠(∞:ℝ≥0∞))).tendsto.comp hlim
  obtain ⟨A,hA,hAb⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_pos_norm_le
  refine ⟨(eLpNorm f P μ).toReal+A,add_nonneg ENNReal.toReal_nonneg hA.le,?_⟩
  intro j
  have hwN : (eLpNorm (w j) P μ).toReal≤A := by
    have hb := hAb ((eLpNorm (w j) P μ).toReal) (mem_range_self j)
    simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using hb
  have hs := eLpNorm_add_le hf.1 (hw j).1 hP
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top,(hw j).eLpNorm_ne_top⟩) hs
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top (hw j).eLpNorm_ne_top] at hr
  linarith only [hr,hwN]

set_option maxHeartbeats 1600000 in
theorem tendsto_eLpNorm_naturalGradientMap_of_strong_Lp
    {n : ℕ} {p : ℝ} (hp : 2≤p) {μ : Measure (Space n)} [IsFiniteMeasure μ]
    {g : ℕ → Space n → Space n} {h : Space n → Space n}
    (hg : ∀ j,MemLp (g j) (ENNReal.ofReal p) μ) (hh : MemLp h (ENNReal.ofReal p) μ)
    (hconv : Tendsto (fun j => eLpNorm (g j-h) (ENNReal.ofReal p) μ) atTop (𝓝 0))
    {ε : ℕ → ℝ} (hεN : ∀ j,ε j≠0) (hεb : ∀ j,|ε j|≤1)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun x => naturalGradientMap p (ε j) (g j x)-
      naturalGradientMap p 0 (h x)) 2 μ) atTop (𝓝 0) := by
  have hp1 : 1≤ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith)
  obtain ⟨N,hN,hNraw⟩ := natural_uniform_norm_of_strong_corrections hp1 hh
    (fun j => (hg j).sub hh) hconv
  have hNbound (j : ℕ) : (eLpNorm (g j) (ENNReal.ofReal p) μ).toReal≤N := by
    have heq : h+(g j-h)=g j := by funext x;simp only [Pi.add_apply,Pi.sub_apply];abel
    simpa only [heq] using hNraw j
  let S := (eLpNorm (fun _ : Space n => (1:ℝ)) (ENNReal.ofReal p) μ).toReal
  let A := (eLpNorm h (ENNReal.ofReal p) μ).toReal
  let C := (p/2)^2*(S+N+A)^(p-2)
  have hC : 0≤C := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by dsimp only [S,A];positivity) _)
  let F : ℕ → Space n → Space n := fun j x => naturalGradientMap p (ε j) (g j x)-naturalGradientMap p (ε j) (h x)
  have hF (j : ℕ) : MemLp (F j) 2 μ := (memLp_naturalGradientMap hp (hg j)).sub (memLp_naturalGradientMap hp hh)
  have hbound (j : ℕ) : (eLpNorm (F j) 2 μ).toReal^2≤C*((eLpNorm (g j-h) (ENNReal.ofReal p) μ).toReal)^2 := by
    have hr := regularized_weighted_square_refined_holder_bound (ε:=ε j) hp (hg j) hh ((hg j).sub hh)
    let W : Space n → ℝ := fun x => ((ε j)^2+(max ‖g j x‖ ‖h x‖)^2)^((p-2)/2)
    have hFI : Integrable (fun x => ‖F j x‖^2) μ := (hF j).integrable_norm_pow (by norm_num)
    have hlow : (∫ x,‖F j x‖^2 ∂μ)≤(p/2)^2*(∫ x,W x*‖(g j-h) x‖^2 ∂μ) := by
      rw [←integral_const_mul]
      apply integral_mono hFI (hr.1.const_mul ((p/2)^2))
      intro x
      simpa only [F,W,Pi.sub_apply,mul_assoc] using naturalGradientMap_difference_sq_le hp (hεN j) (g j x) (h x)
    have hAε : (eLpNorm (fun _ : Space n => |ε j|) (ENNReal.ofReal p) μ).toReal≤S := by
      have h1 : MemLp (fun _ : Space n => (1:ℝ)) (ENNReal.ofReal p) μ := memLp_const _
      apply ENNReal.toReal_mono h1.eLpNorm_ne_top
      exact eLpNorm_mono_ae (Eventually.of_forall (fun _ => by
        simpa only [Real.norm_eq_abs,abs_abs,abs_one] using hεb j))
    have hcbase : (eLpNorm (fun _ : Space n => |ε j|) (ENNReal.ofReal p) μ).toReal+
        (eLpNorm (g j) (ENNReal.ofReal p) μ).toReal+(eLpNorm h (ENNReal.ofReal p) μ).toReal≤S+N+A := by
      dsimp only [A];linarith only [hAε,hNbound j]
    have hcpow := Real.rpow_le_rpow (by positivity) hcbase (by linarith : 0≤p-2)
    have he : (eLpNorm (F j) 2 μ).toReal^2=∫ x,‖F j x‖^2 ∂μ := by
      simpa only [eLpNorm_norm] using natural_integral_sq_norm (hF j).norm
    rw [he]
    calc
      _≤(p/2)^2*(∫ x,W x*‖(g j-h) x‖^2 ∂μ) := hlow
      _≤(p/2)^2*(_*((eLpNorm (g j-h) (ENNReal.ofReal p) μ).toReal)^2) :=
        mul_le_mul_of_nonneg_left hr.2 (sq_nonneg _)
      _≤(p/2)^2*((S+N+A)^(p-2)*((eLpNorm (g j-h) (ENNReal.ofReal p) μ).toReal)^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcpow (sq_nonneg _)) (sq_nonneg _)
      _=_ := by dsimp only [C];ring
  have hreal : Tendsto (fun j => (eLpNorm (g j-h) (ENNReal.ofReal p) μ).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero] using
      (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞)≠(∞:ℝ≥0∞))).tendsto.comp hconv
  have hupper : Tendsto (fun j => C*((eLpNorm (g j-h) (ENNReal.ofReal p) μ).toReal)^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2≠0),mul_zero] using (hreal.pow 2).const_mul C
  have hsq : Tendsto (fun j => (eLpNorm (F j) 2 μ).toReal^2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper (fun _ => sq_nonneg _) hbound
  have hrealF : Tendsto (fun j => (eLpNorm (F j) 2 μ).toReal) atTop (𝓝 0) := by
    have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def,Real.sqrt_sq ENNReal.toReal_nonneg,Real.sqrt_zero] using ht
  have hfirst : Tendsto (fun j => eLpNorm (F j) 2 μ) atTop (𝓝 0) := by
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hrealF
    simp only [ENNReal.ofReal_zero] at he
    exact he.congr' (Eventually.of_forall (fun j => ENNReal.ofReal_toReal (hF j).eLpNorm_ne_top))
  have hfixed := tendsto_eLpNorm_naturalGradientMap_parameter_sub_zero hp hh hεb hε
  have hsum : Tendsto (fun j => eLpNorm (F j) 2 μ+
      eLpNorm (fun x => naturalGradientMap p (ε j) (h x)-naturalGradientMap p 0 (h x)) 2 μ)
      atTop (𝓝 0) := by simpa only [add_zero] using hfirst.add hfixed
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro j
  have hf2 : MemLp (fun x => naturalGradientMap p (ε j) (h x)-naturalGradientMap p 0 (h x)) 2 μ :=
    (memLp_naturalGradientMap hp hh).sub (memLp_naturalGradientMap hp hh)
  have htri := eLpNorm_add_le (hF j).1 hf2.1 (by norm_num : (1:ℝ≥0∞)≤2)
  have heq : (F j+fun x => naturalGradientMap p (ε j) (h x)-naturalGradientMap p 0 (h x))=
      (fun x => naturalGradientMap p (ε j) (g j x)-naturalGradientMap p 0 (h x)) := by
    funext x
    simp only [F,Pi.add_apply]
    abel
  rw [heq] at htri
  exact htri

end BMCompactPDE
#print axioms BMCompactPDE.tendsto_eLpNorm_naturalGradientMap_of_strong_Lp
