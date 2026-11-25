import RegEnergyMinimization

/-! Genuine all-p weighted Young absorption used in the weak Caccioppoli
estimate. No regularity estimate or comparison conclusion is a premise. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal Topology
namespace BMCompactPDE

/-- Integer-power cutoffs can use any real exponent m>=p in the absorption
algebra; m is specialized to a sufficiently large integer when constructing
smooth compactly supported test functions. -/
theorem cutoff_young_absorption {p m η a b : ℝ}
    (hp : 1 < p) (hm : p ≤ m) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    m * η^(m-1) * a^(p-1) * b ≤
      ((p-1)/p) * (η^m * a^p) + (m^p/p) * b^p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp1 : 0 < p-1 := sub_pos.mpr hp
  have hm0 : 0 < m := hp0.trans_le hm
  have hq0 : 0 < p/(p-1) := div_pos hp0 hp1
  have hexp : m ≤ (m-1)*(p/(p-1)) := by
    rw [←mul_div_assoc,le_div_iff₀ hp1]
    nlinarith
  have hη : η^((m-1)*(p/(p-1))) ≤ η^m :=
    Real.rpow_le_rpow_of_exponent_ge' hη0 hη1 hm0.le hexp
  have hcancel : (p-1)*(p/(p-1))=p := by field_simp
  have hA : (η^(m-1)*a^(p-1))^(p/(p-1)) ≤ η^m*a^p := by
    rw [Real.mul_rpow (Real.rpow_nonneg hη0 _) (Real.rpow_nonneg ha _),
      ←Real.rpow_mul hη0,←Real.rpow_mul ha,hcancel]
    exact mul_le_mul_of_nonneg_right hη (Real.rpow_nonneg ha _)
  have hY := Real.young_inequality_of_nonneg
    (mul_nonneg (Real.rpow_nonneg hη0 (m-1)) (Real.rpow_nonneg ha (p-1)))
    (mul_nonneg hm0.le hb) (Real.HolderConjugate.conjExponent hp).symm
  change (η^(m-1)*a^(p-1))*(m*b) ≤
    (η^(m-1)*a^(p-1))^(p/(p-1))/(p/(p-1))+(m*b)^p/p at hY
  calc
    m*η^(m-1)*a^(p-1)*b = (η^(m-1)*a^(p-1))*(m*b) := by ring
    _ ≤ (η^(m-1)*a^(p-1))^(p/(p-1))/(p/(p-1))+(m*b)^p/p := hY
    _ ≤ (η^m*a^p)/(p/(p-1))+(m*b)^p/p :=
      add_le_add (div_le_div_of_nonneg_right hA hq0.le) le_rfl
    _ = ((p-1)/p)*(η^m*a^p)+(m^p/p)*b^p := by
      rw [Real.mul_rpow hm0.le hb]
      field_simp
      <;> ring

/-- The actual nonlinear flux cross term is controlled by the p-energy
absorption above, in every real inner-product space. -/
theorem cutoff_flux_cross_absorption {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {p m η z : ℝ}
    (hp : 1 < p) (hm : p ≤ m) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (g v : E) :
    -(m * η^(m-1) * z * inner ℝ (pFlux p g) v) ≤
      ((p-1)/p)*(η^m*‖g‖^p)+(m^p/p)*(|z|^p*‖v‖^p) := by
  have hm0 : 0 ≤ m := (zero_lt_one.trans hp).le.trans hm
  have hc : 0 ≤ m * η^(m-1) := mul_nonneg hm0 (Real.rpow_nonneg hη0 _)
  have hinner : |inner ℝ (pFlux p g) v| ≤ ‖g‖^(p-1)*‖v‖ := by
    simpa only [norm_pFlux hp] using abs_real_inner_le_norm (pFlux p g) v
  have hzinner : -(z * inner ℝ (pFlux p g) v) ≤ |z| * (‖g‖^(p-1)*‖v‖) := by
    calc
      -(z * inner ℝ (pFlux p g) v) ≤ |z * inner ℝ (pFlux p g) v| := neg_le_abs _
      _ = |z| * |inner ℝ (pFlux p g) v| := abs_mul _ _
      _ ≤ |z| * (‖g‖^(p-1)*‖v‖) := mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
  have hb := mul_le_mul_of_nonneg_left hzinner hc
  have hy := cutoff_young_absorption hp hm hη0 hη1 (norm_nonneg g)
    (mul_nonneg (abs_nonneg z) (norm_nonneg v))
  rw [Real.mul_rpow (abs_nonneg z) (norm_nonneg v)] at hy
  calc
    -(m * η^(m-1) * z * inner ℝ (pFlux p g) v) =
        (m * η^(m-1)) * (-(z * inner ℝ (pFlux p g) v)) := by ring
    _ ≤ (m * η^(m-1)) * (|z| * (‖g‖^(p-1)*‖v‖)) := hb
    _ = m*η^(m-1)*‖g‖^(p-1)*(|z| * ‖v‖) := by ring
    _ ≤ ((p-1)/p)*(η^m*‖g‖^p)+(m^p/p)*(|z|^p*‖v‖^p) := hy

end BMCompactPDE
#print axioms BMCompactPDE.cutoff_young_absorption
#print axioms BMCompactPDE.cutoff_flux_cross_absorption
