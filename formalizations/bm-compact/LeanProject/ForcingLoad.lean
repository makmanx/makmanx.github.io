import ForcingGlobal

/-! The ordinary integral of a genuine W0 function is a bounded load
functional of its actual weak gradient. Constants come from proved Poincare
and finite-measure Holder; no load-continuity premise is introduced. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem exists_W0_source_load_bound {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) {Ω : Set (Space n)}
    (hΩb : Bornology.IsBounded Ω) :
    ∃ K : ℝ, 0≤K ∧ ∀ {w : Space n → ℝ} {gw : Space n → Space n},
      ZeroBoundarySobolevPair p Ω w gw →
        |∫ x in Ω,w x|≤K*(eLpNorm gw (ENNReal.ofReal p) (volume.restrict Ω)).toReal := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  obtain ⟨C,hC⟩ := exists_W0_Lp_poincare_constant hp hpn hΩb
  let μ := volume.restrict Ω
  let M : ℝ≥0∞ := μ univ^(1-1/p)
  have hp0 : 0<p := zero_lt_one.trans hp
  have he : 0≤1-1/p := sub_nonneg.mpr ((div_le_iff₀ hp0).mpr (by linarith))
  have hM : M≠(∞ : ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top μ univ)
  refine ⟨(C : ℝ)*M.toReal,mul_nonneg C.coe_nonneg ENNReal.toReal_nonneg,?_⟩
  intro w gw hw
  have hLp : eLpNorm w 1 μ≤eLpNorm w (ENNReal.ofReal p) μ*M := by
    simpa only [ENNReal.toReal_one,ENNReal.toReal_ofReal hp0.le,div_one] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (ENNReal.one_le_ofReal.mpr hp.le) hw.1.2.1.1
  have hI : ‖∫ x,w x ∂μ‖ₑ≤eLpNorm w 1 μ := by
    simpa only [eLpNorm_one_eq_lintegral_enorm] using
      (enorm_integral_le_lintegral_enorm (μ := μ) w)
  have hbound : ‖∫ x,w x ∂μ‖ₑ≤
      ((C : ℝ≥0∞)*eLpNorm gw (ENNReal.ofReal p) μ)*M :=
    hI.trans (hLp.trans (mul_le_mul_left (hC hw) M))
  have hfinite : ((C : ℝ≥0∞)*eLpNorm gw (ENNReal.ofReal p) μ)*M≠(∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hw.1.2.2.1.eLpNorm_ne_top) hM
  have hr := ENNReal.toReal_mono hfinite hbound
  simp only [toReal_enorm,Real.norm_eq_abs,ENNReal.toReal_mul,ENNReal.coe_toReal] at hr
  convert hr using 1 <;> ring

end BMCompactPDE
#print axioms BMCompactPDE.exists_W0_source_load_bound
