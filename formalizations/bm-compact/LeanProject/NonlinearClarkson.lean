import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Convex.Uniform

/-! Actual Clarkson inequality for Hilbert-valued Lp, initially p>=2. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal NNReal
namespace BMCompactNonlinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sq_rpow_half (z : E) (p : ℝ) :
    (‖z‖ ^ 2) ^ (p/2) = ‖z‖ ^ p := by
  rw [← Real.rpow_natCast_mul (norm_nonneg z) 2 (p/2)]
  congr 1
  ring

theorem hilbert_midpoint_clarkson {p : ℝ} (hp : 2≤p) (x y : E) :
    ‖(1/2:ℝ) • (x+y)‖ ^ p + ‖(1/2:ℝ) • (x-y)‖ ^ p ≤
      (‖x‖ ^ p + ‖y‖ ^ p)/2 := by
  have hr : 1≤p/2 := by linarith
  have hpar : ‖(1/2:ℝ) • (x+y)‖ ^ 2 + ‖(1/2:ℝ) • (x-y)‖ ^ 2 =
      (1/2:ℝ)*‖x‖ ^ 2 + (1/2:ℝ)*‖y‖ ^ 2 := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hh := parallelogram_law_with_norm ℝ x y
    nlinarith
  have hfirst := Real.add_rpow_le_rpow_add
    (sq_nonneg ‖(1/2:ℝ) • (x+y)‖) (sq_nonneg ‖(1/2:ℝ) • (x-y)‖) hr
  rw [hpar] at hfirst
  have hsecond := (convexOn_rpow hr).2 (sq_nonneg ‖x‖) (sq_nonneg ‖y‖)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simp only [smul_eq_mul] at hsecond
  rw [norm_sq_rpow_half, norm_sq_rpow_half] at hfirst hsecond
  exact hfirst.trans (by nlinarith [hsecond])

section Lp
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)]

theorem lp_norm_rpow_eq_integral (hp : 0<p) (f : Lp E (ENNReal.ofReal p) μ) :
    ‖f‖ ^ p = ∫ x, ‖f x‖ ^ p ∂μ := by
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm hq0 ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hp.le]
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact Real.rpow_inv_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)) hp.ne'

theorem lp_norm_rpow_integrable (hp : 0<p) (f : Lp E (ENNReal.ofReal p) μ) :
    Integrable (fun x => ‖f x‖ ^ p) μ := by
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  simpa only [ENNReal.toReal_ofReal hp.le] using
    (Lp.memLp f).integrable_norm_rpow hq0 ENNReal.ofReal_ne_top

theorem lp_midpoint_clarkson (hp : 2≤p) (f g : Lp E (ENNReal.ofReal p) μ) :
    ‖(1/2:ℝ) • (f+g)‖ ^ p + ‖(1/2:ℝ) • (f-g)‖ ^ p ≤
      (‖f‖ ^ p + ‖g‖ ^ p)/2 := by
  have hp0 : 0<p := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hp
  let m := (1/2:ℝ) • (f+g)
  let d := (1/2:ℝ) • (f-g)
  have hm := lp_norm_rpow_integrable hp0 m
  have hd := lp_norm_rpow_integrable hp0 d
  have hf := lp_norm_rpow_integrable hp0 f
  have hg := lp_norm_rpow_integrable hp0 g
  rw [lp_norm_rpow_eq_integral hp0,lp_norm_rpow_eq_integral hp0,
    lp_norm_rpow_eq_integral hp0,lp_norm_rpow_eq_integral hp0]
  rw [← integral_add hm hd,← integral_add hf hg,← integral_div]
  apply integral_mono_ae (hm.add hd) ((hf.add hg).div_const 2)
  filter_upwards [Lp.coeFn_smul (1/2:ℝ) (f+g), Lp.coeFn_smul (1/2:ℝ) (f-g),
    Lp.coeFn_add f g, Lp.coeFn_sub f g] with x hmx hdx hfg hfg'
  simpa only [m,d,Pi.smul_apply, Pi.add_apply, Pi.sub_apply, hmx,hdx,hfg,hfg'] using
    hilbert_midpoint_clarkson hp (f x) (g x)

theorem lp_uniformConvexSpace (hp : 2≤p) :
    UniformConvexSpace (Lp E (ENNReal.ofReal p) μ) where
  uniform_convex := by
    intro ε hε
    have hp0 : 0<p := lt_of_lt_of_le (by norm_num : (0:ℝ)<2) hp
    by_cases hε2 : ε≤2
    · let a : ℝ := (ε/2)^p
      let b : ℝ := (1-a)^p⁻¹
      have ha0 : 0<a := Real.rpow_pos_of_pos (by positivity) _
      have ha1 : a≤1 := by
        have hh := Real.rpow_le_rpow (by positivity : (0:ℝ)≤ε/2)
          (by linarith : ε/2≤1) hp0.le
        simpa only [Real.one_rpow] using hh
      have hba : 0≤1-a := sub_nonneg.mpr ha1
      have hb1 : b<1 := by
        apply (Real.rpow_inv_lt_iff_of_pos hba zero_le_one hp0).2
        simpa only [Real.one_rpow] using sub_lt_self 1 ha0
      refine ⟨2-2*b,by linarith,?_⟩
      intro f hf g hg hfg
      have hcl := lp_midpoint_clarkson hp f g
      have hcl' : ‖(1/2:ℝ) • (f+g)‖^p + ‖(1/2:ℝ) • (f-g)‖^p ≤ 1 := by
        simpa only [hf,hg,Real.one_rpow,one_add_one_eq_two,div_self (by norm_num : (2:ℝ)≠0)] using hcl
      have hhalf : ε/2 ≤ ‖(1/2:ℝ) • (f-g)‖ := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
        linarith
      have had : a≤‖(1/2:ℝ) • (f-g)‖^p :=
        Real.rpow_le_rpow (by positivity) hhalf hp0.le
      have hmb : ‖(1/2:ℝ) • (f+g)‖ ≤ b := by
        apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hba hp0).2
        linarith
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)] at hmb
      linarith
    · refine ⟨1,zero_lt_one,?_⟩
      intro f hf g hg hfg
      have hh := norm_sub_le f g
      rw [hf,hg,one_add_one_eq_two] at hh
      exact ((lt_of_not_ge hε2).not_ge (hfg.trans hh)).elim

end Lp

end BMCompactNonlinear
#print axioms BMCompactNonlinear.norm_sq_rpow_half
#print axioms BMCompactNonlinear.hilbert_midpoint_clarkson
#print axioms BMCompactNonlinear.lp_norm_rpow_eq_integral
#print axioms BMCompactNonlinear.lp_norm_rpow_integrable
#print axioms BMCompactNonlinear.lp_midpoint_clarkson
#print axioms BMCompactNonlinear.lp_uniformConvexSpace
