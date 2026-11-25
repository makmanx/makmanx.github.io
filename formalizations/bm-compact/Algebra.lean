import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Exact algebraic substeps of BM_Compact_Final.tex.

The normalization statements below implement the arithmetic in the proof of
Lemma `lem5.5` (source lines 1463–1475). They do not assume or prove any
capacitary Brunn–Minkowski inequality.

The final min bound implements the scalar inequality used in Lemma `lem5.2`,
between equations (5.14) and (5.15) (source lines 1397–1398).
-/

set_option autoImplicit false

noncomputable section

namespace BMCompact

/-- The positive scale `A = λ a₁ + (1-λ) a₂` of Lemma 4.5 (`lem5.5`). -/
def normalizationScale (t a b : ℝ) : ℝ := t * a + (1 - t) * b

/-- The normalized weight `λ'' = λ a₁ / A` of Lemma 4.5 (`lem5.5`). -/
def normalizationWeight (t a b : ℝ) : ℝ := t * a / normalizationScale t a b

theorem normalizationScale_pos {t a b : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (ha : 0 < a) (hb : 0 < b) :
    0 < normalizationScale t a b := by
  exact add_pos (mul_pos ht ha) (mul_pos (sub_pos.mpr ht1) hb)

theorem normalizationWeight_pos {t a b : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (ha : 0 < a) (hb : 0 < b) :
    0 < normalizationWeight t a b := by
  exact div_pos (mul_pos ht ha) (normalizationScale_pos ht ht1 ha hb)

theorem normalizationWeight_lt_one {t a b : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (ha : 0 < a) (hb : 0 < b) :
    normalizationWeight t a b < 1 := by
  apply (div_lt_one (normalizationScale_pos ht ht1 ha hb)).2
  change t * a < t * a + (1 - t) * b
  exact lt_add_of_pos_right _ (mul_pos (sub_pos.mpr ht1) hb)

theorem normalizationWeight_complement {t a b : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (ha : 0 < a) (hb : 0 < b) :
    1 - normalizationWeight t a b =
      (1 - t) * b / normalizationScale t a b := by
  have hA : normalizationScale t a b ≠ 0 :=
    ne_of_gt (normalizationScale_pos ht ht1 ha hb)
  unfold normalizationWeight
  apply (eq_div_iff hA).2
  field_simp [hA]
  simp only [normalizationScale]
  ring

theorem normalization_left_coefficient {t a b : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (ha : 0 < a) (hb : 0 < b) :
    normalizationWeight t a b * a⁻¹ = (normalizationScale t a b)⁻¹ * t := by
  have hA : normalizationScale t a b ≠ 0 :=
    ne_of_gt (normalizationScale_pos ht ht1 ha hb)
  unfold normalizationWeight
  field_simp [ne_of_gt ha, hA]

theorem normalization_right_coefficient {t a b : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (ha : 0 < a) (hb : 0 < b) :
    (1 - normalizationWeight t a b) * b⁻¹ =
      (normalizationScale t a b)⁻¹ * (1 - t) := by
  have hA : normalizationScale t a b ≠ 0 :=
    ne_of_gt (normalizationScale_pos ht ht1 ha hb)
  rw [normalizationWeight_complement ht ht1 ha hb]
  field_simp [ne_of_gt hb, hA]

/-- The pointwise vector rescaling identity in Lemma 4.5 (`lem5.5`). -/
theorem normalization_vector_identity {V : Type*} [AddCommGroup V] [Module ℝ V]
    {t a b : ℝ} (ht : 0 < t) (ht1 : t < 1) (ha : 0 < a) (hb : 0 < b)
    (y z : V) :
    normalizationWeight t a b • (a⁻¹ • y) +
        (1 - normalizationWeight t a b) • (b⁻¹ • z) =
      (normalizationScale t a b)⁻¹ • (t • y + (1 - t) • z) := by
  simp only [smul_add, smul_smul]
  rw [normalization_left_coefficient ht ht1 ha hb,
    normalization_right_coefficient ht ht1 ha hb]

/-- The set rescaling identity in Lemma 4.5 (`lem5.5`), with the two original witnesses explicit. -/
theorem normalization_set_identity {V : Type*} [AddCommGroup V] [Module ℝ V]
    {t a b : ℝ} (ht : 0 < t) (ht1 : t < 1) (ha : 0 < a) (hb : 0 < b)
    (E F : Set V) :
    {x : V | ∃ y ∈ E, ∃ z ∈ F,
        x = normalizationWeight t a b • (a⁻¹ • y) +
          (1 - normalizationWeight t a b) • (b⁻¹ • z)} =
      (fun v : V => (normalizationScale t a b)⁻¹ • v) ''
        {v : V | ∃ y ∈ E, ∃ z ∈ F, v = t • y + (1 - t) • z} := by
  ext x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    refine ⟨t • y + (1 - t) • z, ⟨y, hy, z, hz, rfl⟩, ?_⟩
    exact (normalization_vector_identity ht ht1 ha hb y z).symm
  · rintro ⟨v, ⟨y, hy, z, hz, rfl⟩, rfl⟩
    exact ⟨y, hy, z, hz, (normalization_vector_identity ht ht1 ha hb y z).symm⟩

/-- Scalar min estimate used in the Taylor expansion proof of Lemma 4.2 (`lem5.2`). -/
theorem min_ge_weighted_sub_abs (u v w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    min u v ≥ w * u + (1 - w) * v - |u - v| := by
  rcases le_total u v with huv | hvu
  · rw [min_eq_left huv, abs_of_nonpos (sub_nonpos.mpr huv)]
    nlinarith [mul_nonneg hw0 (sub_nonneg.mpr huv)]
  · rw [min_eq_right hvu, abs_of_nonneg (sub_nonneg.mpr hvu)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr hvu)]

#print axioms normalizationScale_pos
#print axioms normalizationWeight_pos
#print axioms normalizationWeight_lt_one
#print axioms normalizationWeight_complement
#print axioms normalization_left_coefficient
#print axioms normalization_right_coefficient
#print axioms normalization_vector_identity
#print axioms normalization_set_identity
#print axioms min_ge_weighted_sub_abs

end BMCompact
