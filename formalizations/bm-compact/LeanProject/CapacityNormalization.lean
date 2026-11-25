import CapacityAffine
import Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! The manuscript's normalization step (printed Lemma4.5, label lem5.5)
for the actual variational capacity. The genuine homogeneity law is proved
in CapacityAffine, not supplied as an axiom. The minimum inequality in this
reduction is an explicitly open analytic premise, not a completed PDE proof. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal ContDiff Pointwise
namespace BMCompactCapacityV2

def subcriticalCapacityRoot {n : ℕ} (p : ℝ) (K : Set (Space n)) : ℝ :=
  (variationalCapacity p K ^ (1 / ((n : ℝ) - p))).toReal

theorem variationalCapacity_root_dilate {n : ℕ} (p : ℝ) (hp : 0 < p)
    (hpn : p < (n : ℝ)) {ρ : ℝ} (hρ : 0 < ρ) (K : Set (Space n)) :
    variationalCapacity p (ρ • K) ^ (1 / ((n : ℝ) - p)) =
      ENNReal.ofReal ρ * variationalCapacity p K ^ (1 / ((n : ℝ) - p)) := by
  have hnp : 0 < (n : ℝ) - p := sub_pos.mpr hpn
  rw [variationalCapacity_dilate p hp hρ,
    ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg zero_le_one hnp.le),
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hρ _),
    ← Real.rpow_mul hρ.le]
  have hexp : ((n : ℝ) - p) * (1 / ((n : ℝ) - p)) = 1 := by field_simp [hnp.ne']
  rw [hexp, Real.rpow_one]

theorem subcriticalCapacityRoot_dilate {n : ℕ} (p : ℝ) (hp : 0 < p)
    (hpn : p < (n : ℝ)) {ρ : ℝ} (hρ : 0 < ρ) (K : Set (Space n)) :
    subcriticalCapacityRoot p (ρ • K) = ρ * subcriticalCapacityRoot p K := by
  unfold subcriticalCapacityRoot
  rw [variationalCapacity_root_dilate p hp hpn hρ, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hρ.le]

theorem subcriticalCapacityRoot_translate {n : ℕ} (p : ℝ) (hp : 0 < p)
    (K : Set (Space n)) (a : Space n) :
    subcriticalCapacityRoot p (K + {a}) = subcriticalCapacityRoot p K := by
  simp only [subcriticalCapacityRoot, variationalCapacity_translate p hp]

theorem subcriticalCapacityRoot_nonneg {n : ℕ} (p : ℝ) (K : Set (Space n)) :
    0 ≤ subcriticalCapacityRoot p K := ENNReal.toReal_nonneg

theorem normalization_pointwise_set_identity {n : ℕ} {t a b : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (ha : 0 < a) (hb : 0 < b)
    (E F : Set (Space n)) :
    BMCompact.normalizationWeight t a b • (a⁻¹ • E) +
      (1 - BMCompact.normalizationWeight t a b) • (b⁻¹ • F) =
    (BMCompact.normalizationScale t a b)⁻¹ • (t • E + (1 - t) • F) := by
  simp only [smul_smul, smul_add]
  rw [BMCompact.normalization_left_coefficient ht ht1 ha hb,
    BMCompact.normalization_right_coefficient ht ht1 ha hb]

/-- If the min inequality is proved for compact sets, positive-capacity inputs
give the weighted sum inequality by the paper's actual capacity normalization.
The min inequality is the remaining analytic comparison input. -/
theorem subcritical_BM_of_min_comparison {n : ℕ} (p : ℝ) (hp : 0 < p)
    (hpn : p < (n : ℝ))
    (hmin : ∀ (K L : Set (Space n)), IsCompact K → IsCompact L →
      K.Nonempty → L.Nonempty → ∀ s : ℝ, 0 < s → s < 1 →
      min (subcriticalCapacityRoot p K) (subcriticalCapacityRoot p L) ≤
        subcriticalCapacityRoot p (s • K + (1 - s) • L))
    (E F : Set (Space n)) (hE : IsCompact E) (hF : IsCompact F)
    (hEn : E.Nonempty) (hFn : F.Nonempty)
    (ha : 0 < subcriticalCapacityRoot p E) (hb : 0 < subcriticalCapacityRoot p F)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    t * subcriticalCapacityRoot p E + (1 - t) * subcriticalCapacityRoot p F ≤
      subcriticalCapacityRoot p (t • E + (1 - t) • F) := by
  let a := subcriticalCapacityRoot p E
  let b := subcriticalCapacityRoot p F
  let A := BMCompact.normalizationScale t a b
  let s := BMCompact.normalizationWeight t a b
  have hA : 0 < A := BMCompact.normalizationScale_pos ht ht1 ha hb
  have hs : 0 < s := BMCompact.normalizationWeight_pos ht ht1 ha hb
  have hs1 : s < 1 := BMCompact.normalizationWeight_lt_one ht ht1 ha hb
  have hEn' : (a⁻¹ • E).Nonempty := by
    obtain ⟨x,hx⟩ := hEn
    exact ⟨a⁻¹ • x,⟨x,hx,rfl⟩⟩
  have hFn' : (b⁻¹ • F).Nonempty := by
    obtain ⟨x,hx⟩ := hFn
    exact ⟨b⁻¹ • x,⟨x,hx,rfl⟩⟩
  have hcmp := hmin (a⁻¹ • E) (b⁻¹ • F) (hE.smul a⁻¹) (hF.smul b⁻¹)
    hEn' hFn' s hs hs1
  have he : subcriticalCapacityRoot p (a⁻¹ • E) = 1 := by
    rw [subcriticalCapacityRoot_dilate p hp hpn (inv_pos.mpr ha)]
    exact inv_mul_cancel₀ ha.ne'
  have hf : subcriticalCapacityRoot p (b⁻¹ • F) = 1 := by
    rw [subcriticalCapacityRoot_dilate p hp hpn (inv_pos.mpr hb)]
    exact inv_mul_cancel₀ hb.ne'
  have hsets : s • (a⁻¹ • E) + (1 - s) • (b⁻¹ • F) =
      A⁻¹ • (t • E + (1 - t) • F) :=
    normalization_pointwise_set_identity ht ht1 ha hb E F
  rw [he, hf, min_self, hsets,
    subcriticalCapacityRoot_dilate p hp hpn (inv_pos.mpr hA)] at hcmp
  have hmul := mul_le_mul_of_nonneg_left hcmp hA.le
  have hdone : A ≤ subcriticalCapacityRoot p (t • E + (1-t) • F) := by
    simpa only [mul_one, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] using! hmul
  simpa only [A, BMCompact.normalizationScale, a, b] using! hdone

end BMCompactCapacityV2
#print axioms BMCompactCapacityV2.variationalCapacity_root_dilate
#print axioms BMCompactCapacityV2.subcriticalCapacityRoot_dilate
#print axioms BMCompactCapacityV2.subcriticalCapacityRoot_translate
#print axioms BMCompactCapacityV2.subcriticalCapacityRoot_nonneg
#print axioms BMCompactCapacityV2.normalization_pointwise_set_identity
#print axioms BMCompactCapacityV2.subcritical_BM_of_min_comparison
