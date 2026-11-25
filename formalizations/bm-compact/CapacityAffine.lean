import CapacityAffineEnergy

/-! Translation invariance and positive homogeneity of the actual variational
p-capacity, with smooth compactly supported competitors transported explicitly.
This proves the subcritical part of manuscript equation (4.1); it does not
assume any Brunn--Minkowski inequality or Green-function identification. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal ContDiff Pointwise

namespace BMCompactCapacityV2

theorem Admissible.dilateTest_univ {n : ℕ} {K : Set (Space n)}
    {f : Space n → ℝ} (hf : Admissible K univ f) {ρ : ℝ} (hρ : ρ ≠ 0) :
    Admissible (ρ • K) univ (dilateTest ρ f) := by
  refine ⟨contDiff_dilateTest hf.1 ρ, hasCompactSupport_dilateTest hf.2.1 hρ,
    subset_univ _, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  simpa only [dilateTest, smul_smul, inv_mul_cancel₀ hρ, one_smul] using hf.2.2.2 y hy

theorem Admissible.translateTest_univ {n : ℕ} {K : Set (Space n)}
    {f : Space n → ℝ} (hf : Admissible K univ f) (a : Space n) :
    Admissible (K + {a}) univ (translateTest a f) := by
  refine ⟨contDiff_translateTest hf.1 a, hasCompactSupport_translateTest hf.2.1 a,
    subset_univ _, ?_⟩
  rintro x ⟨y, hy, z, hz, rfl⟩
  have hz' : z = a := mem_singleton_iff.mp hz
  simpa only [translateTest, hz', add_sub_cancel_right] using hf.2.2.2 y hy

theorem variationalCapacity_dilate_le {n : ℕ} (p : ℝ) (hp : 0 < p)
    {ρ : ℝ} (hρ : 0 < ρ) (K : Set (Space n)) :
    variationalCapacity p (ρ • K) ≤
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * variationalCapacity p K := by
  have hzero : ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ _))
  unfold variationalCapacity relativeCapacity
  rw [ENNReal.mul_iInf_of_ne hzero ENNReal.ofReal_ne_top]
  refine le_iInf fun f => ?_
  rw [ENNReal.mul_iInf_of_ne hzero ENNReal.ofReal_ne_top]
  refine le_iInf fun hf => ?_
  exact (relativeCapacity_le_energy p (hf.dilateTest_univ hρ.ne')).trans_eq
    (pEnergy_dilateTest p hp hρ hf.1 hf.2.1)

theorem variationalCapacity_dilate {n : ℕ} (p : ℝ) (hp : 0 < p)
    {ρ : ℝ} (hρ : 0 < ρ) (K : Set (Space n)) :
    variationalCapacity p (ρ • K) =
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * variationalCapacity p K := by
  apply le_antisymm (variationalCapacity_dilate_le p hp hρ K)
  have hb := variationalCapacity_dilate_le p hp (inv_pos.mpr hρ) (ρ • K)
  have hset : ρ⁻¹ • (ρ • K) = K := by
    rw [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
  rw [hset, Real.inv_rpow hρ.le,
    ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hρ _)] at hb
  have hzero : ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ _))
  calc
    ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * variationalCapacity p K ≤
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) *
        ((ENNReal.ofReal (ρ ^ ((n : ℝ) - p)))⁻¹ *
          variationalCapacity p (ρ • K)) := mul_le_mul le_rfl hb zero_le zero_le
    _ = variationalCapacity p (ρ • K) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hzero ENNReal.ofReal_ne_top, one_mul]

theorem variationalCapacity_translate_le {n : ℕ} (p : ℝ) (hp : 0 < p)
    (K : Set (Space n)) (a : Space n) :
    variationalCapacity p (K + {a}) ≤ variationalCapacity p K := by
  unfold variationalCapacity relativeCapacity
  refine le_iInf fun f => le_iInf fun hf => ?_
  exact (relativeCapacity_le_energy p (hf.translateTest_univ a)).trans_eq
    (pEnergy_translateTest p hp a hf.1 hf.2.1)

theorem variationalCapacity_translate {n : ℕ} (p : ℝ) (hp : 0 < p)
    (K : Set (Space n)) (a : Space n) :
    variationalCapacity p (K + {a}) = variationalCapacity p K := by
  apply le_antisymm (variationalCapacity_translate_le p hp K a)
  have hb := variationalCapacity_translate_le p hp (K + {a}) (-a)
  have hset : (K + {a}) + {-a} = K := by
    simp only [add_assoc, singleton_add_singleton, add_neg_cancel, singleton_zero, add_zero]
  simpa only [hset] using hb

theorem variationalCapacity_affine {n : ℕ} (p : ℝ) (hp : 0 < p)
    {ρ : ℝ} (hρ : 0 < ρ) (K : Set (Space n)) (a : Space n) :
    variationalCapacity p (ρ • K + {a}) =
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * variationalCapacity p K := by
  rw [variationalCapacity_translate p hp, variationalCapacity_dilate p hp hρ]

end BMCompactCapacityV2

#print axioms BMCompactCapacityV2.Admissible.dilateTest_univ
#print axioms BMCompactCapacityV2.Admissible.translateTest_univ
#print axioms BMCompactCapacityV2.variationalCapacity_dilate_le
#print axioms BMCompactCapacityV2.variationalCapacity_dilate
#print axioms BMCompactCapacityV2.variationalCapacity_translate_le
#print axioms BMCompactCapacityV2.variationalCapacity_translate
#print axioms BMCompactCapacityV2.variationalCapacity_affine
