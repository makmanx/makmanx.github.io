import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Attributed native Morrey estimate adapted from accepted public Prove2Me proofs by Mazecto. Exact original sources, accepted receipts and structural transformations are preserved in MorreyReusedDependencies. Private prerequisites add zero extra exported proofs. No original proof body is rewritten. -/
noncomputable section
set_option autoImplicit false

section MorreySource0

open MeasureTheory Set Metric
open scoped ENNReal
set_option autoImplicit false

private theorem MeasureTheory.lintegral_mul_segment_eq_dilation_adjoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [SecondCountableTopology E] (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    [SFinite μ] (f h : E → ENNReal) (hf : Measurable f) (hh : Measurable h) :
    (∫⁻ z, h z * (∫⁻ t in Icc (0 : ℝ) 1, f (t • z)) ∂μ) =
      ∫⁻ y, f y * (∫⁻ t in Ioc (0 : ℝ) 1,
        ENNReal.ofReal ((t ^ Module.finrank ℝ E)⁻¹) * h (t⁻¹ • y)) ∂μ := by
  have hi : volume.restrict (Icc (0 : ℝ) 1) = volume.restrict (Ioc (0 : ℝ) 1) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  simp only [hi]
  have hc (z : E) : h z * (∫⁻ t in Ioc (0 : ℝ) 1, f (t • z)) =
      ∫⁻ t in Ioc (0 : ℝ) 1, h z * f (t • z) :=
    (lintegral_const_mul _ (hf.comp (measurable_id.smul measurable_const))).symm
  simp only [hc]
  rw [lintegral_lintegral_swap]
  · calc
      (∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z, h z * f (t • z) ∂μ) =
          ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y,
            f y * (ENNReal.ofReal ((t ^ Module.finrank ℝ E)⁻¹) * h (t⁻¹ • y)) ∂μ := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro t ht
        let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 t ht.1.ne')).toMeasurableEquiv
        have he : (∫⁻ y, h (t⁻¹ • y) * f y ∂Measure.map e μ) =
            ∫⁻ z, h z * f (t • z) ∂μ := by
          rw [lintegral_map_equiv]
          congr 1
          ext z
          simp [e, smul_smul, inv_mul_cancel₀ ht.1.ne']
        dsimp only
        rw [← he]
        change (∫⁻ y, h (t⁻¹ • y) * f y ∂Measure.map (t • ·) μ) = _
        rw [Measure.map_addHaar_smul μ ht.1.ne', lintegral_smul_measure,
          abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht.1.le _)), smul_eq_mul]
        rw [← lintegral_const_mul]
        · apply lintegral_congr
          intro y
          ac_rfl
        · exact ((hh.comp (measurable_const.smul measurable_id)).mul hf)
      _ = _ := by
        rw [lintegral_lintegral_swap]
        · congr 1
          ext y
          rw [lintegral_const_mul]
          exact ((measurable_id.pow_const _).inv.ennreal_ofReal.mul
            (hh.comp (measurable_id.inv.smul measurable_const)))
        · exact ((hf.comp measurable_snd).mul
            (((measurable_fst.pow_const _).inv.ennreal_ofReal).mul
              (hh.comp (measurable_fst.inv.smul measurable_snd)))).aemeasurable
  · exact ((hh.comp measurable_fst).mul
      (hf.comp (measurable_snd.smul measurable_fst))).aemeasurable

end MorreySource0

section MorreySource1

open MeasureTheory Set Metric
open scoped ENNReal
set_option autoImplicit false

private theorem MeasureTheory.segment_ball_rayKernel_bound {n : ℕ} (hn : 0 < n)
    (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) :
    (∫⁻ t in Ioc (0 : ℝ) 1,
      ENNReal.ofReal ((t ^ n)⁻¹) *
        (if t⁻¹ * ρ < r then ENNReal.ofReal (t⁻¹ * ρ) else 0)) ≤
      ENNReal.ofReal (r ^ n / (n : ℝ) * ρ ^ (1 - (n : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < ρ / r := div_pos hρ hr
  have he : -(n : ℝ) - 1 < -1 := by linarith
  calc
    _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, (Ioi (ρ / r)).indicator
        (fun t => ENNReal.ofReal (ρ * t ^ (-(n : ℝ) - 1))) t := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro t ht
      by_cases htr : t⁻¹ * ρ < r
      · have hat : ρ / r < t := by
          rw [div_lt_iff₀ hr]
          have := (inv_mul_lt_iff₀ ht.1).mp htr
          nlinarith
        rw [if_pos htr, indicator_of_mem (show t ∈ Ioi (ρ / r) from hat),
          ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg ht.1.le _))]
        apply le_of_eq
        congr 1
        rw [Real.rpow_sub ht.1, Real.rpow_neg ht.1.le, Real.rpow_natCast,
          Real.rpow_one]
        field_simp
      · simp [htr]
    _ ≤ ∫⁻ t, (Ioi (ρ / r)).indicator
        (fun t => ENNReal.ofReal (ρ * t ^ (-(n : ℝ) - 1))) t :=
      lintegral_mono' Measure.restrict_le_self (le_refl _)
    _ = ENNReal.ofReal (ρ * (- (ρ / r) ^ (-(n : ℝ) - 1 + 1) /
        (-(n : ℝ) - 1 + 1))) := by
      rw [lintegral_indicator measurableSet_Ioi,
        ← ofReal_integral_eq_lintegral_ofReal
          ((integrableOn_Ioi_rpow_of_lt he ha).const_mul ρ)
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact mul_nonneg hρ.le (Real.rpow_nonneg (ha.trans ht).le _)),
        integral_const_mul, integral_Ioi_rpow_of_lt he ha]
    _ = _ := by
      congr 1
      rw [show -(n : ℝ) - 1 + 1 = -(n : ℝ) by ring,
        Real.rpow_neg ha.le, Real.div_rpow hρ.le hr.le, Real.rpow_natCast,
        Real.rpow_sub hρ, Real.rpow_one, Real.rpow_natCast]
      field_simp
      exact (Real.rpow_natCast ρ n)


private theorem MeasureTheory.lintegral_segment_ball_le_rieszPotential {n : ℕ} (hn : 0 < n) :
    ∃ C : NNReal, ∀ g : EuclideanSpace ℝ (Fin n) → ENNReal,
      Measurable g → ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ z in Metric.ball x r, ENNReal.ofReal ‖z - x‖ *
        (∫⁻ t in Set.Icc (0 : ℝ) 1, g (x + t • (z - x)))) ≤
        volume (Metric.ball x r) * (C : ENNReal) *
          (∫⁻ z in Metric.ball x r, g z *
            ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let V : ℝ := volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hV : 0 < V := by
    exact ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne'
      (measure_ball_lt_top.ne)
  refine ⟨(1 / ((n : ℝ) * V)).toNNReal, fun g hg x r hr => ?_⟩
  let f : EuclideanSpace ℝ (Fin n) → ENNReal :=
    (ball 0 r).indicator (fun y => g (x + y))
  let h : EuclideanSpace ℝ (Fin n) → ENNReal :=
    (ball 0 r).indicator (fun y => ENNReal.ofReal ‖y‖)
  have hf : Measurable f := (hg.comp (measurable_const.add measurable_id)).indicator
    measurableSet_ball
  have hh : Measurable h := measurable_id.norm.ennreal_ofReal.indicator measurableSet_ball
  have hadj := MeasureTheory.lintegral_mul_segment_eq_dilation_adjoint volume f h hf hh
  have hleft : (∫⁻ z in ball x r, ENNReal.ofReal ‖z - x‖ *
      (∫⁻ t in Icc (0 : ℝ) 1, g (x + t • (z - x)))) =
      ∫⁻ z, h z * (∫⁻ t in Icc (0 : ℝ) 1, f (t • z)) := by
    have ht := (measurePreserving_add_left volume x).setLIntegral_comp_preimage_emb
      (Homeomorph.addLeft x).measurableEmbedding
      (fun z => ENNReal.ofReal ‖z - x‖ *
        (∫⁻ t in Icc (0 : ℝ) 1, g (x + t • (z - x)))) (ball x r)
    have hs : (fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' ball x r = ball 0 r := by
      ext y
      simp [mem_ball, dist_eq_norm]
    rw [hs] at ht
    rw [← ht, ← lintegral_indicator measurableSet_ball]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ ball 0 r
    · simp only [indicator_of_mem hz, h, add_sub_cancel_left]
      congr 1
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      have htz : t • z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        have hz' : ‖z‖ < r := mem_ball_zero_iff.mp hz
        exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz'
      simp [f, htz]
    · simp [h, hz]
  have hright : (∫⁻ y, f y * (∫⁻ t in Ioc (0 : ℝ) 1,
      ENNReal.ofReal ((t ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))⁻¹) * h (t⁻¹ • y))) ≤
      ENNReal.ofReal (r ^ n / (n : ℝ)) *
        (∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin n)) r,
          g (x + y) * ENNReal.ofReal (‖y‖ ^ (1 - (n : ℝ)))) := by
    have hm : Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
        g (x + y) * ENNReal.ofReal (‖y‖ ^ (1 - (n : ℝ)))) :=
      (hg.comp (measurable_const.add measurable_id)).mul
        ((measurable_id.norm.pow_const _).ennreal_ofReal)
    rw [← lintegral_const_mul _ hm,
      ← lintegral_indicator measurableSet_ball]
    apply lintegral_mono_ae
    have hzero : ∀ᵐ y : EuclideanSpace ℝ (Fin n), y ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hzero] with y hy0
    by_cases hyr : y ∈ ball 0 r
    · simp only [f, indicator_of_mem hyr]
      have hk := MeasureTheory.segment_ball_rayKernel_bound hn r ‖y‖ hr (norm_pos_iff.mpr hy0)
      have heq : (∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal ((t ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))⁻¹) * h (t⁻¹ • y)) =
          ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal ((t ^ n)⁻¹) *
            (if t⁻¹ * ‖y‖ < r then ENNReal.ofReal (t⁻¹ * ‖y‖) else 0) := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro t ht
        dsimp only
        have hnorm : ‖t⁻¹ • y‖ = t⁻¹ * ‖y‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht.1)]
        by_cases htmem : t⁻¹ • y ∈ ball 0 r
        · rw [show h (t⁻¹ • y) = ENNReal.ofReal ‖t⁻¹ • y‖ from
            indicator_of_mem htmem _, hnorm, if_pos (by simpa [mem_ball_zero_iff, hnorm] using htmem)]
          simp
        · rw [show h (t⁻¹ • y) = 0 from indicator_of_notMem htmem _,
            if_neg (by simpa [mem_ball_zero_iff, hnorm] using htmem)]
          simp
      rw [heq]
      calc
        _ ≤ g (x + y) * ENNReal.ofReal (r ^ n / (n : ℝ) * ‖y‖ ^ (1 - (n : ℝ))) :=
          mul_le_mul (le_refl _) hk (by positivity) (by positivity)
        _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]; ac_rfl
    · simp [f, hyr]
  have hvol : volume (ball x r) *
      (((1 / ((n : ℝ) * V)).toNNReal : NNReal) : ENNReal) =
      ENNReal.ofReal (r ^ n / (n : ℝ)) := by
    rw [Measure.addHaar_ball volume x hr.le]
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    rw [← ENNReal.ofReal_toReal (measure_ball_lt_top.ne)]
    change ENNReal.ofReal (r ^ n) * ENNReal.ofReal V *
      ENNReal.ofReal (1 / ((n : ℝ) * V)) = _
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have htrans : (∫⁻ y in ball (0 : EuclideanSpace ℝ (Fin n)) r,
      g (x + y) * ENNReal.ofReal (‖y‖ ^ (1 - (n : ℝ)))) =
      ∫⁻ z in ball x r, g z * ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ))) := by
    have ht := (measurePreserving_add_left volume x).setLIntegral_comp_preimage_emb
      (Homeomorph.addLeft x).measurableEmbedding
      (fun z => g z * ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) (ball x r)
    have hs : (fun y : EuclideanSpace ℝ (Fin n) => x + y) ⁻¹' ball x r = ball 0 r := by
      ext y
      simp [mem_ball, dist_eq_norm]
    simpa [hs, add_sub_cancel_left] using ht
  rw [hleft, hadj, hvol]
  exact hright.trans_eq (congrArg (ENNReal.ofReal (r ^ n / (n : ℝ)) * ·) htrans)

end MorreySource1

section MorreySource2

open MeasureTheory Set Metric
set_option autoImplicit false

private theorem MeasureTheory.integral_norm_rpow_ball (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : 0 < α)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ (α - n)) (ball 0 R) ∧
      (∫ z : EuclideanSpace ℝ (Fin n) in ball 0 R, ‖z‖ ^ (α - n)) =
        (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * R ^ α / α := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hp : (n - 1 : ℕ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn, Nat.cast_one]
  have heq : ∀ r : ℝ, 0 < r → r ^ (n - 1) * r ^ (α - n) = r ^ (α - 1) := by
    intro r hr
    rw [← Real.rpow_natCast, ← Real.rpow_add hr, hp]
    congr 1
    ring
  have hi : IntegrableOn (fun r : ℝ => r ^ (α - 1)) (Ioo 0 R) := by
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hR]
    linarith
  have hiw : IntegrableOn (fun r : ℝ => r ^ (n - 1) * r ^ (α - n)) (Ioo 0 R) :=
    hi.congr_fun (fun r hr => (heq r hr.1).symm) measurableSet_Ioo
  refine ⟨?_, ?_⟩
  · exact (integrableOn_fun_norm_addHaar (E := EuclideanSpace ℝ (Fin n))
      volume (f := fun r : ℝ => r ^ (α - n))).2
        (by simpa [finrank_euclideanSpace, smul_eq_mul] using hiw)
  · have hrad := integral_fun_norm_addHaar
      (E := EuclideanSpace ℝ (Fin n)) volume ((Iio R).indicator (fun r : ℝ => r ^ (α - n)))
    have hleft : (fun z : EuclideanSpace ℝ (Fin n) =>
        (Iio R).indicator (fun r : ℝ => r ^ (α - n)) ‖z‖) =
        (ball 0 R).indicator (fun z => ‖z‖ ^ (α - n)) := by
      funext z
      simp [indicator]
    have hright : (fun r : ℝ => r ^ (n - 1) *
        (Iio R).indicator (fun r : ℝ => r ^ (α - n)) r) =
        (Iio R).indicator (fun r : ℝ => r ^ (n - 1) * r ^ (α - n)) := by
      funext r
      by_cases hr : r < R <;> simp [indicator, hr]
    simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul] at hrad
    rw [hleft, integral_indicator measurableSet_ball, hright,
      setIntegral_indicator measurableSet_Iio] at hrad
    have hset : Ioi (0 : ℝ) ∩ Iio R = Ioo 0 R := by ext r; simp
    rw [hset, setIntegral_congr_fun measurableSet_Ioo (fun r hr => heq r hr.1)] at hrad
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
      integral_rpow (Or.inl (by linarith : -1 < α - 1))] at hrad
    simpa [show α - 1 + 1 = α by ring, Real.zero_rpow hα.ne', sub_zero, mul_div_assoc,
      mul_assoc]
      using hrad

end MorreySource2

section MorreySource3

open MeasureTheory Set
set_option autoImplicit false

private theorem MeasureTheory.ofReal_abs_sub_le_segment_lintegral_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (x z : E) :
    ENNReal.ofReal |f x - f z| ≤ ENNReal.ofReal ‖z - x‖ *
      (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ‖gradient f (x + t • (z - x))‖) := by
  let γ : ℝ → E := fun t => x + t • (z - x)
  let D : ℝ → ℝ := fun t => fderiv ℝ f (γ t) (z - x)
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hD : Continuous D :=
    ((hf.continuous_fderiv (by norm_num)).comp hγ).clm_apply continuous_const
  have hderiv (t : ℝ) : HasDerivAt (fun s => f (γ s)) (D t) t := by
    have hp : HasDerivAt γ (z - x) t := by
      simpa [γ] using ((hasDerivAt_id t).smul_const (z - x)).const_add x
    exact ((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).comp_hasDerivAt t hp
  have hFTC : (∫ t in (0 : ℝ)..1, D t) = f z - f x := by
    simpa [γ] using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) (hD.intervalIntegrable 0 1)
  have hnorm (t : ℝ) : ‖D t‖ ≤ ‖z - x‖ * ‖gradient f (γ t)‖ := by
    dsimp [D]
    rw [← inner_gradient_left]
    simpa [mul_comm] using norm_inner_le_norm (𝕜 := ℝ) (gradient f (γ t)) (z - x)
  calc
    ENNReal.ofReal |f x - f z| = ‖∫ t in Icc (0 : ℝ) 1, D t‖ₑ := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, hFTC]
      simp [Real.enorm_eq_ofReal_abs, abs_sub_comm]
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖D t‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal ‖z - x‖ * ENNReal.ofReal ‖gradient f (γ t)‖ := by
      apply lintegral_mono
      intro t
      change ‖D t‖ₑ ≤ ENNReal.ofReal ‖z - x‖ * ENNReal.ofReal ‖gradient f (γ t)‖
      simpa only [ofReal_norm, ENNReal.ofReal_mul (norm_nonneg _)] using
        ENNReal.ofReal_le_ofReal (hnorm t)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]


end MorreySource3

section MorreySource4

open MeasureTheory
set_option autoImplicit false

private theorem HunterPDE.Sobolev.centered_ball_oscillation_le_potential {n : ℕ} (hn : 0 < n) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 f → ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ z in Metric.ball x r, ENNReal.ofReal |f x - f z|) ≤
        volume (Metric.ball x r) * (C : ENNReal) *
          (∫⁻ z in Metric.ball x r, ENNReal.ofReal ‖gradient f z‖ *
            ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) := by
  obtain ⟨C, hC⟩ := MeasureTheory.lintegral_segment_ball_le_rieszPotential hn
  refine ⟨C, fun f hf x r hr => ?_⟩
  have hg : Measurable (fun z => ENNReal.ofReal ‖gradient f z‖) := by
    have hc := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (hf.continuous_fderiv (by norm_num))
    exact ENNReal.measurable_ofReal.comp hc.norm.measurable
  calc
    (∫⁻ z in Metric.ball x r, ENNReal.ofReal |f x - f z|) ≤
        ∫⁻ z in Metric.ball x r, ENNReal.ofReal ‖z - x‖ *
          (∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ‖gradient f (x + t • (z - x))‖) :=
      lintegral_mono fun z => MeasureTheory.ofReal_abs_sub_le_segment_lintegral_gradient f hf x z
    _ ≤ _ := hC (fun z => ENNReal.ofReal ‖gradient f z‖) hg x r hr

end MorreySource4

section MorreySource5

open MeasureTheory Set Metric
set_option autoImplicit false

private theorem MeasureTheory.lintegral_mul_rieszKernel_ball_le {n : ℕ} {p : ℝ} (hn : 0 < n) (hnp : (n : ℝ) < p) :
    ∃ C : NNReal, ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
      AEStronglyMeasurable g volume →
      ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ z in Metric.ball x r, ENNReal.ofReal |g z| *
        ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) ≤
        (C : ENNReal) * eLpNorm g (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x r)) *
            ENNReal.ofReal (r ^ (1 - (n : ℝ) / p)) := by
  have hn1 : 1 ≤ n := hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hp1 : 1 < p := lt_of_le_of_lt hnR hnp
  have hp : 0 < p := by linarith
  let q : ℝ := p / (p - 1)
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq : 0 < q := hpq.symm.pos
  let α : ℝ := n + (1 - (n : ℝ)) * q
  have hαeq : α = (p - n) / (p - 1) := by
    dsimp [α, q]
    field_simp [hp.ne', (sub_pos.mpr hp1).ne']
    ring
  have hα : 0 < α := by rw [hαeq]; exact div_pos (sub_pos.mpr hnp) (sub_pos.mpr hp1)
  have hexp : α / q = 1 - (n : ℝ) / p := by
    rw [hαeq]
    dsimp [q]
    field_simp [hp.ne', (sub_pos.mpr hp1).ne']
  let K : ℝ := (n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) / α
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨(K ^ (1 / q)).toNNReal, fun g hg x r hr => ?_⟩
  let μ := volume.restrict (ball x r)
  have hkmeas : Measurable (fun z : EuclideanSpace ℝ (Fin n) => ‖z - x‖ ^ (1 - (n : ℝ))) :=
    (continuous_id.sub continuous_const).norm.measurable.pow_const _
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (hg.aemeasurable.norm.ennreal_ofReal.restrict)
    (hkmeas.ennreal_ofReal.aemeasurable)
  have hnorm : (∫⁻ z, ENNReal.ofReal |g z| ^ p ∂μ) ^ (1 / p) =
      eLpNorm g (ENNReal.ofReal p) μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top]
    simp [ENNReal.toReal_ofReal hp.le, Real.enorm_eq_ofReal_abs]
  have hrad := MeasureTheory.integral_norm_rpow_ball n hn1 α hα r hr
  have hzero : (∫⁻ z : EuclideanSpace ℝ (Fin n) in ball 0 r,
      ENNReal.ofReal (‖z‖ ^ (α - n))) = ENNReal.ofReal (K * r ^ α) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hrad.1
      (Filter.Eventually.of_forall (fun z => Real.rpow_nonneg (norm_nonneg z) _)), hrad.2]
    congr 1
    dsimp [K]
    ring
  have htrans : (∫⁻ z : EuclideanSpace ℝ (Fin n) in ball x r,
      ENNReal.ofReal (‖z - x‖ ^ (α - n))) = ENNReal.ofReal (K * r ^ α) := by
    have ht := (measurePreserving_sub_right volume x).setLIntegral_comp_preimage_emb
      (Homeomorph.subRight x).measurableEmbedding
      (fun z : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (‖z‖ ^ (α - n))) (ball 0 r)
    have hs : (fun z : EuclideanSpace ℝ (Fin n) => z - x) ⁻¹' ball 0 r = ball x r := by
      ext z
      simp [mem_ball, dist_eq_norm]
    rw [hs] at ht
    exact ht.trans hzero
  have hpower : (∫⁻ z, ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ))) ^ q ∂μ) =
      ENNReal.ofReal (K * r ^ α) := by
    rw [← htrans]
    apply lintegral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    dsimp only
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hq.le,
      ← Real.rpow_mul (norm_nonneg _)]
    congr 2
    dsimp [α]
    ring
  have hscale : (ENNReal.ofReal (K * r ^ α)) ^ (1 / q) =
      ((K ^ (1 / q)).toNNReal : ENNReal) * ENNReal.ofReal (r ^ (1 - (n : ℝ) / p)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hK (Real.rpow_nonneg hr.le _)) (by positivity),
      Real.mul_rpow hK (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le,
      show α * (1 / q) = 1 - (n : ℝ) / p by simpa only [div_eq_mul_inv, one_mul] using hexp, ENNReal.ofReal_mul (Real.rpow_nonneg hK _)]
    rfl
  simp only [Real.norm_eq_abs] at hholder
  rw [hnorm, hpower, hscale] at hholder
  simpa only [Pi.mul_apply, μ, mul_comm, mul_left_comm, mul_assoc] using hholder




end MorreySource5

section MorreySource6

open MeasureTheory MeasureTheory.Measure

private theorem HunterPDE.Sobolev.ball_averaged_oscillation_le {n : ℕ} {p : ℝ}
    (hn : 0 < n) (hnp : (n : ℝ) < p) :
    ∃ C : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 f → ∀ (a : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      ∀ x ∈ Metric.ball a r,
        (∫⁻ z in Metric.ball a r, ENNReal.ofReal |f x - f z|) ≤
          volume (Metric.ball a r) * (C : ENNReal) *
            eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
              (volume.restrict (Metric.ball a (3 * r))) *
            ENNReal.ofReal (r ^ (1 - (n : ℝ) / p)) := by
  obtain ⟨A, hA⟩ := HunterPDE.Sobolev.centered_ball_oscillation_le_potential hn
  obtain ⟨D, hD⟩ := MeasureTheory.lintegral_mul_rieszKernel_ball_le hn hnp
  refine ⟨2 ^ n * A * D * 2, fun f hf a r hr x hx => ?_⟩
  have hr2 : 0 < 2 * r := by linarith
  have hsub : Metric.ball a r ⊆ Metric.ball x (2 * r) := by
    intro z hz
    change dist z x < 2 * r
    calc
      dist z x ≤ dist z a + dist a x := dist_triangle _ _ _
      _ < r + r := add_lt_add hz (by simpa [dist_comm] using hx)
      _ = _ := by ring
  have hsub3 : Metric.ball x (2 * r) ⊆ Metric.ball a (3 * r) := by
    intro z hz
    change dist z a < 3 * r
    calc
      dist z a ≤ dist z x + dist x a := dist_triangle _ _ _
      _ < 2 * r + r := add_lt_add hz hx
      _ = _ := by ring
  have hgm : AEStronglyMeasurable (fun z => ‖gradient f z‖) volume := by
    have hc := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp
      (hf.continuous_fderiv (by norm_num))
    exact hc.norm.aestronglyMeasurable
  have hpot := hD (fun z => ‖gradient f z‖) hgm x (2 * r) hr2
  simp only [abs_norm] at hpot
  have hG : eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x (2 * r))) ≤
      eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
        (volume.restrict (Metric.ball a (3 * r))) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hsub3 le_rfl)
  have hvol : volume (Metric.ball x (2 * r)) =
      (2 : ENNReal) ^ n * volume (Metric.ball a r) := by
    rw [addHaar_ball_of_pos volume x hr2, addHaar_ball_of_pos volume a hr]
    simp only [finrank_euclideanSpace, Fintype.card_fin, mul_pow,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ n), ENNReal.ofReal_pow
        (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    ring
  have hp : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg n) hnp
  have hα : 1 - (n : ℝ) / p ≤ 1 :=
    sub_le_self _ (div_nonneg (Nat.cast_nonneg _) hp.le)
  have hscale : ENNReal.ofReal ((2 * r) ^ (1 - (n : ℝ) / p)) ≤
      2 * ENNReal.ofReal (r ^ (1 - (n : ℝ) / p)) := by
    have h : (2 * r) ^ (1 - (n : ℝ) / p) ≤ 2 * r ^ (1 - (n : ℝ) / p) := by
      rw [Real.mul_rpow (by norm_num) hr.le]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr.le _)
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal h
  calc
    _ ≤ ∫⁻ z in Metric.ball x (2 * r), ENNReal.ofReal |f x - f z| :=
      lintegral_mono_set hsub
    _ ≤ volume (Metric.ball x (2 * r)) * (A : ENNReal) *
        (∫⁻ z in Metric.ball x (2 * r), ENNReal.ofReal ‖gradient f z‖ *
          ENNReal.ofReal (‖z - x‖ ^ (1 - (n : ℝ)))) := hA f hf x (2 * r) hr2
    _ ≤ volume (Metric.ball x (2 * r)) * (A : ENNReal) *
        ((D : ENNReal) * eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball x (2 * r))) *
            ENNReal.ofReal ((2 * r) ^ (1 - (n : ℝ) / p))) :=
      by simpa only [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_left hpot (volume (Metric.ball x (2 * r)) * (A : ENNReal))
    _ ≤ volume (Metric.ball x (2 * r)) * (A : ENNReal) *
        ((D : ENNReal) * eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
          (volume.restrict (Metric.ball a (3 * r)))) *
            (2 * ENNReal.ofReal (r ^ (1 - (n : ℝ) / p))) := by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul'
        (mul_le_mul_left (mul_le_mul_left hG (D : ENNReal))
          (volume (Metric.ball x (2 * r)) * (A : ENNReal))) hscale
    _ = _ := by
      rw [hvol]
      simp only [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat]
      ring

end MorreySource6

section MorreySource7

open MeasureTheory

theorem BMCompactMorreyReuse.morrey_increment_of_contDiff {n : ℕ} {p : ℝ} (hnp : (n : ℝ) < p) :
    ∃ A : NNReal, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 f →
      ∀ x y, ENNReal.ofReal |f x - f y| ≤
        (A : ENNReal) * eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p) volume *
          ENNReal.ofReal (‖x - y‖ ^ (1 - (n : ℝ) / p)) := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨0, fun f _ x y => ?_⟩
    have hxy : x = y := Subsingleton.elim _ _
    simp [hxy]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨C, hC⟩ := HunterPDE.Sobolev.ball_averaged_oscillation_le hnpos hnp
  refine ⟨4 * C, fun f hf x y => ?_⟩
  by_cases hxy : x = y
  · simp [hxy]
  let d : ℝ := ‖x - y‖
  let α : ℝ := 1 - (n : ℝ) / p
  let G : ENNReal := eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p) volume
  let B := Metric.ball x (2 * d)
  let v : ENNReal := volume B
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hr : 0 < 2 * d := by positivity
  have hxB : x ∈ B := by simpa [B] using hr
  have hyB : y ∈ B := by
    change dist y x < 2 * d
    rw [dist_comm, dist_eq_norm]
    change d < 2 * d
    linarith
  have hv0 : v ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hvt : v ≠ ⊤ := measure_ball_lt_top.ne
  have hG : eLpNorm (fun z => ‖gradient f z‖) (ENNReal.ofReal p)
      (volume.restrict (Metric.ball x (3 * (2 * d)))) ≤ G :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hbound (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ B) :
      (∫⁻ z in B, ENNReal.ofReal |f w - f z|) ≤
        v * (C : ENNReal) * G * ENNReal.ofReal ((2 * d) ^ α) := by
    exact (hC f hf x (2 * d) hr w hw).trans
      (mul_le_mul_left (mul_le_mul_right hG _) _)
  have hmeas : Measurable (fun z => ENNReal.ofReal |f x - f z|) :=
    (continuous_const.sub hf.continuous).abs.measurable.ennreal_ofReal
  have htriangle : ENNReal.ofReal |f x - f y| * v ≤
      v * (C : ENNReal) * G * ENNReal.ofReal ((2 * d) ^ α) +
        v * (C : ENNReal) * G * ENNReal.ofReal ((2 * d) ^ α) := by
    calc
      _ = ∫⁻ _z in B, ENNReal.ofReal |f x - f y| := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ z in B, (ENNReal.ofReal |f x - f z| + ENNReal.ofReal |f y - f z|) := by
        apply lintegral_mono
        intro z
        calc
          _ ≤ ENNReal.ofReal (|f x - f z| + |f y - f z|) :=
            ENNReal.ofReal_le_ofReal (by simpa [abs_sub_comm] using abs_sub_le (f x) (f z) (f y))
          _ = _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ = (∫⁻ z in B, ENNReal.ofReal |f x - f z|) +
          (∫⁻ z in B, ENNReal.ofReal |f y - f z|) := lintegral_add_left hmeas _
      _ ≤ _ := add_le_add (hbound x hxB) (hbound y hyB)
  have hcancel : ENNReal.ofReal |f x - f y| ≤
      (C : ENNReal) * G * ENNReal.ofReal ((2 * d) ^ α) +
        (C : ENNReal) * G * ENNReal.ofReal ((2 * d) ^ α) := by
    apply (ENNReal.mul_le_mul_iff_left hv0 hvt).mp
    simpa only [add_mul, mul_assoc, mul_comm, mul_left_comm] using htriangle
  have hp : 0 < p := lt_of_le_of_lt (Nat.cast_nonneg _) hnp
  have hα : α ≤ 1 := sub_le_self _ (div_nonneg (Nat.cast_nonneg _) hp.le)
  have hscale : (2 * d) ^ α ≤ 2 * d ^ α := by
    rw [Real.mul_rpow (by norm_num) hd.le]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd.le _)
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα
  have hscale' : ENNReal.ofReal ((2 * d) ^ α) ≤ 2 * ENNReal.ofReal (d ^ α) := by
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal hscale
  calc
    _ ≤ _ := hcancel
    _ ≤ (C : ENNReal) * G * (2 * ENNReal.ofReal (d ^ α)) +
          (C : ENNReal) * G * (2 * ENNReal.ofReal (d ^ α)) :=
      add_le_add (mul_le_mul_right hscale' _) (mul_le_mul_right hscale' _)
    _ = _ := by
      simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
      ring

end MorreySource7

#print axioms BMCompactMorreyReuse.morrey_increment_of_contDiff
