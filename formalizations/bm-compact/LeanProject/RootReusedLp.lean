import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! Reused public Prove2Me proof bodies. Original records and exact original
source hashes are in RootReusedLp.provenance.json. Mathematical statements and
proofs retained; only module imports and declaration/dependency names changed.
These three existing proofs are not counted as newly authored results. -/
set_option autoImplicit false
namespace BMCompactReuse
section Reusedlintegral_minkowski

open MeasureTheory MeasureTheory.Measure

theorem lintegral_minkowski {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {q : ℝ} (hq : 1 < q) (G : α → β → ENNReal)
    (hG : AEMeasurable (Function.uncurry G) (μ.prod ν))
    (hbound : (∫⁻ y, eLpNorm (fun x => G x y) (ENNReal.ofReal q) μ ∂ν) < ⊤) :
    eLpNorm (fun x => ∫⁻ y, G x y ∂ν) (ENNReal.ofReal q) μ ≤
      ∫⁻ y, eLpNorm (fun x => G x y) (ENNReal.ofReal q) μ ∂ν := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hp0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq0).ne'
  have norm_formula (f : α → ENNReal) :
      eLpNorm f (ENNReal.ofReal q) μ = (∫⁻ x, f x ^ q ∂μ) ^ (1 / q) := by
    simp [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le, enorm_eq_self, one_div]
  suffices core : ∀ K : α → β → ENNReal,
      Measurable (Function.uncurry K) →
      (∫⁻ y, (∫⁻ x, K x y ^ q ∂μ) ^ (1 / q) ∂ν) < ⊤ →
      (∫⁻ x, (∫⁻ y, K x y ∂ν) ^ q ∂μ) ^ (1 / q) ≤
        ∫⁻ y, (∫⁻ x, K x y ^ q ∂μ) ^ (1 / q) ∂ν by
    let K : α → β → ENNReal := fun x y => hG.mk (Function.uncurry G) (x, y)
    have heq : Function.uncurry G =ᵐ[μ.prod ν] Function.uncurry K := hG.ae_eq_mk
    have heqx := ae_ae_of_ae_prod heq
    have heqy := ae_ae_of_ae_prod
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp heq)
    have hrhs : (∫⁻ y, eLpNorm (fun x => G x y) (ENNReal.ofReal q) μ ∂ν) =
        ∫⁻ y, (∫⁻ x, K x y ^ q ∂μ) ^ (1 / q) ∂ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [heqy] with y hy
      change (fun x => G x y) =ᵐ[μ] (fun x => K x y) at hy
      rw [eLpNorm_congr_ae hy, norm_formula]
    have hlhs : eLpNorm (fun x => ∫⁻ y, G x y ∂ν) (ENNReal.ofReal q) μ =
        (∫⁻ x, (∫⁻ y, K x y ∂ν) ^ q ∂μ) ^ (1 / q) := by
      have hi : (fun x => ∫⁻ y, G x y ∂ν) =ᵐ[μ] (fun x => ∫⁻ y, K x y ∂ν) :=
        heqx.mono fun x hx => lintegral_congr_ae hx
      rw [eLpNorm_congr_ae hi, norm_formula]
    rw [hlhs, hrhs]
    exact core K hG.measurable_mk (hrhs ▸ hbound)
  intro K hK hb
  let a : β → ENNReal := fun y => (∫⁻ x, K x y ^ q ∂μ) ^ (1 / q)
  let B : ENNReal := ∫⁻ y, a y ∂ν
  let W : α → β → ENNReal := fun x y => K x y ^ q * a y ^ (1 - q)
  have ha : Measurable a := (hK.pow_const q).lintegral_prod_left.pow_const _
  have hW : Measurable (Function.uncurry W) :=
    (hK.pow_const q).mul ((ha.comp measurable_snd).pow_const _)
  have hapow (y : β) : a y ^ q = ∫⁻ x, K x y ^ q ∂μ := by
    dsimp [a]
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have hatop : ∀ᵐ y ∂ν, a y ≠ ⊤ :=
    (ae_lt_top ha hb.ne).mono fun y hy => hy.ne
  have hsection : ∀ᵐ y ∂ν, ∀ᵐ x ∂μ,
      W x y ^ (1 / q) * a y ^ (1 - 1 / q) = K x y := by
    filter_upwards [hatop] with y hytop
    by_cases hy0 : a y = 0
    · have hz : ∫⁻ x, K x y ^ q ∂μ = 0 := by rw [← hapow, hy0]; simp [hq0]
      have hzAE := ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero hq0.le
        (hK.of_uncurry_right.aemeasurable) hz
      filter_upwards [hzAE] with x hx
      simp [W, hx, hq0]
    · filter_upwards [] with x
      dsimp [W]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      have hqq : q * (1 / q) = 1 := by field_simp
      have hexp : (1 - q) * (1 / q) + (1 - 1 / q) = 0 := by field_simp; ring
      rw [hqq, ENNReal.rpow_one, mul_assoc,
        ← ENNReal.rpow_add _ _ hy0 hytop, hexp, ENNReal.rpow_zero, mul_one]
  have hsection' : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν,
      W x y ^ (1 / q) * a y ^ (1 - 1 / q) = K x y := by
    apply (ae_ae_comm (μ := μ) (ν := ν)
      (p := fun x y => W x y ^ (1 / q) * a y ^ (1 - 1 / q) = K x y) ?_).mpr hsection
    exact measurableSet_eq_fun
      ((hW.pow_const _).mul ((ha.comp measurable_snd).pow_const _)) hK
  have hWint : (∫⁻ x, ∫⁻ y, W x y ∂ν ∂μ) = B := by
    rw [lintegral_lintegral_swap hW.aemeasurable]
    refine lintegral_congr_ae ?_
    filter_upwards [hatop] with y hytop
    by_cases hy0 : a y = 0
    · have hz : ∫⁻ x, K x y ^ q ∂μ = 0 := by rw [← hapow, hy0]; simp [hq0]
      have hzAE := ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero hq0.le
        (hK.of_uncurry_right.aemeasurable) hz
      calc
        (∫⁻ x, W x y ∂μ) = ∫⁻ x, (0 : ENNReal) ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hzAE] with x hx
          simp [W, hx, hq0]
        _ = a y := by simp [hy0]
    · dsimp [W]
      rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_ne_zero hy0 hytop)]
      rw [← hapow, ← ENNReal.rpow_add _ _ hy0 hytop]
      simp
  have ht : 0 ≤ 1 / q := by positivity
  have hu : 0 ≤ 1 - 1 / q := by
    have : 1 / q < 1 := (div_lt_one hq0).mpr hq
    linarith
  have hpoint : ∀ᵐ x ∂μ, (∫⁻ y, K x y ∂ν) ^ q ≤
      (∫⁻ y, W x y ∂ν) * B ^ (q - 1) := by
    filter_upwards [hsection'] with x hx
    have hholder := ENNReal.lintegral_mul_norm_pow_le (μ := ν) (f := W x) (g := a)
      (hW.of_uncurry_left.aemeasurable) ha.aemeasurable ht hu (by ring)
    have heq : (∫⁻ y, W x y ^ (1 / q) * a y ^ (1 - 1 / q) ∂ν) =
        ∫⁻ y, K x y ∂ν := lintegral_congr_ae hx
    rw [heq] at hholder
    have hr := ENNReal.rpow_le_rpow hholder hq0.le
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hr
    have htq : (1 / q) * q = 1 := by field_simp
    have huq : (1 - 1 / q) * q = q - 1 := by field_simp
    simpa only [htq, huq, ENNReal.rpow_one] using hr
  have hint : (∫⁻ x, (∫⁻ y, K x y ∂ν) ^ q ∂μ) ≤ B ^ q := by
    calc
      _ ≤ ∫⁻ x, (∫⁻ y, W x y ∂ν) * B ^ (q - 1) ∂μ := lintegral_mono_ae hpoint
      _ = B * B ^ (q - 1) := by
        rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hb.ne),
          hWint]
      _ = B ^ q := by
        calc
          B * B ^ (q - 1) = B ^ (1 : ℝ) * B ^ (q - 1) := by rw [ENNReal.rpow_one]
          _ = B ^ (1 + (q - 1)) :=
            (ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith)).symm
          _ = B ^ q := by congr 1; ring
  have hr := ENNReal.rpow_le_rpow hint ht
  rw [← ENNReal.rpow_mul] at hr
  have hqq : q * (1 / q) = 1 := by field_simp
  simpa only [hqq, ENNReal.rpow_one] using hr
end Reusedlintegral_minkowski


section Reusedintegral_minkowski

open MeasureTheory

theorem integral_minkowski {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (F : α → β → ℝ)
    (hF : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν))
    (hFi : ∀ᵐ x ∂μ, Integrable (F x) ν) :
    eLpNorm (fun x => ∫ y, F x y ∂ν) p μ ≤
      ∫⁻ y, eLpNorm (fun x => F x y) p μ ∂ν := by
  by_cases hpone : p = 1
  · subst p
    simp_rw [eLpNorm_one_eq_lintegral_enorm]
    calc
      (∫⁻ x, ‖∫ y, F x y ∂ν‖ₑ ∂μ) ≤ ∫⁻ x, ∫⁻ y, ‖F x y‖ₑ ∂ν ∂μ :=
        lintegral_mono fun x => enorm_integral_le_lintegral_enorm (F x)
      _ = ∫⁻ y, ∫⁻ x, ‖F x y‖ₑ ∂μ ∂ν :=
        lintegral_lintegral_swap hF.enorm
  by_cases htop : (∫⁻ y, eLpNorm (fun x => F x y) p μ ∂ν) = ⊤
  · rw [htop]
    exact le_top
  have hpgt : 1 < p := lt_of_le_of_ne hp (Ne.symm hpone)
  have hq : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).2 hpgt
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop
  have hbound : (∫⁻ y, eLpNorm (fun x => ‖F x y‖ₑ) (ENNReal.ofReal p.toReal) μ ∂ν) < ⊤ := by
    simpa only [hpeq, eLpNorm_enorm] using (lt_top_iff_ne_top.mpr htop)
  have hnonneg := BMCompactReuse.lintegral_minkowski μ ν hq
    (fun x y => ‖F x y‖ₑ) hF.enorm hbound
  simp only [hpeq, eLpNorm_enorm] at hnonneg
  refine le_trans ?_ hnonneg
  apply eLpNorm_mono_enorm
  intro x
  simpa only [enorm_eq_self] using enorm_integral_le_lintegral_enorm (F x)
end Reusedintegral_minkowski


section Reusedscalar_convolution_contraction

open MeasureTheory ContinuousLinearMap
open scoped Convolution

theorem scalar_convolution_contraction {n : ℕ} {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1)
    (d : EuclideanSpace ℝ (Fin n) → ℝ) (hd : MemLp d p volume) :
    eLpNorm (ρ ⋆[lsmul ℝ ℝ, volume] d) p volume ≤ eLpNorm d p volume := by
  let F := fun x y => ρ y * d (x - y)
  have hρi : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρs
  have hc := hρs.convolutionExists_left (lsmul ℝ ℝ) hρc (hd.locallyIntegrable hp)
  have hFi (x) : Integrable (F x) volume := (hc x).integrable
  have hF : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    exact (hρi.aestronglyMeasurable.convolution_integrand
      (μ := volume) (lsmul ℝ ℝ) hd.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun z => by
        simp only [F, Function.uncurry, lsmul_apply, smul_eq_mul])
  have hav := BMCompactReuse.integral_minkowski volume volume hp hptop F hF
    (Filter.Eventually.of_forall hFi)
  change eLpNorm (ρ ⋆[lsmul ℝ ℝ, volume] d) p volume ≤ _ at hav
  refine hav.trans_eq ?_
  have heq (y) : eLpNorm (fun x => F x y) p volume =
      ENNReal.ofReal (ρ y) * eLpNorm d p volume := by
    change eLpNorm ((ρ y) • (fun x => d (x - y))) p volume = _
    rw [eLpNorm_const_smul]
    have hn : ‖ρ y‖ₑ = ENNReal.ofReal (ρ y) := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hρ0 y)]
    rw [hn]
    congr 1
    exact eLpNorm_comp_measurePreserving hd.aestronglyMeasurable
      (measurePreserving_sub_right volume y)
  simp_rw [heq]
  rw [lintegral_mul_const _ hρc.measurable.ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal hρi (Filter.Eventually.of_forall hρ0),
    hρ1, ENNReal.ofReal_one, one_mul]
end Reusedscalar_convolution_contraction

end BMCompactReuse
#print axioms BMCompactReuse.lintegral_minkowski
#print axioms BMCompactReuse.integral_minkowski
#print axioms BMCompactReuse.scalar_convolution_contraction
