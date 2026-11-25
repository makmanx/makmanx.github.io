import CapacityAffine

/-! Simultaneous affine change of variables for the actual condenser capacity.
Both plates/domain are transformed, as required by source equation(9.1)(c).
This does not assert that relative capacity scales if only the inner set moves. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal ContDiff Pointwise
namespace BMCompactCapacityV2

theorem Admissible.dilateTest {n : ℕ} {K O : Set (Space n)} {f : Space n → ℝ}
    (hf : Admissible K O f) {ρ : ℝ} (hρ : ρ ≠ 0) :
    Admissible (ρ • K) (ρ • O) (dilateTest ρ f) := by
  have hu : Admissible K univ f :=
    ⟨hf.1,hf.2.1,subset_univ _,hf.2.2.2⟩
  have hd := hu.dilateTest_univ hρ
  refine ⟨hd.1,hd.2.1,?_,hd.2.2.2⟩
  intro x hx
  have hpre : ρ⁻¹ • x ∈ tsupport f :=
    tsupport_comp_subset_preimage f (continuous_id.const_smul ρ⁻¹) hx
  exact ⟨ρ⁻¹ • x,hf.2.2.1 hpre,by simp only [smul_smul,mul_inv_cancel₀ hρ,one_smul]⟩

theorem Admissible.translateTest {n : ℕ} {K O : Set (Space n)} {f : Space n → ℝ}
    (hf : Admissible K O f) (a : Space n) :
    Admissible (K + {a}) (O + {a}) (translateTest a f) := by
  have hu : Admissible K univ f :=
    ⟨hf.1,hf.2.1,subset_univ _,hf.2.2.2⟩
  have hd := hu.translateTest_univ a
  refine ⟨hd.1,hd.2.1,?_,hd.2.2.2⟩
  intro x hx
  have hpre : x - a ∈ tsupport f :=
    tsupport_comp_subset_preimage f (continuous_id.sub continuous_const) hx
  exact ⟨x-a,hf.2.2.1 hpre,a,mem_singleton a,sub_add_cancel x a⟩

theorem relativeCapacity_dilate_le {n : ℕ} (p : ℝ) (hp : 0 < p)
    {ρ : ℝ} (hρ : 0 < ρ) (K O : Set (Space n)) :
    relativeCapacity p (ρ • K) (ρ • O) ≤
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * relativeCapacity p K O := by
  have hzero : ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ _))
  unfold relativeCapacity
  rw [ENNReal.mul_iInf_of_ne hzero ENNReal.ofReal_ne_top]
  refine le_iInf fun f => ?_
  rw [ENNReal.mul_iInf_of_ne hzero ENNReal.ofReal_ne_top]
  refine le_iInf fun hf => ?_
  have hd := hf.dilateTest hρ.ne'
  apply (relativeCapacity_le_energy p hd).trans_eq
  rw [pEnergy_eq_univ_of_tsupport_subset p hp.ne' hd.2.2.1,
    pEnergy_dilateTest p hp hρ hf.1 hf.2.1,
    pEnergy_eq_univ_of_tsupport_subset p hp.ne' hf.2.2.1]

theorem relativeCapacity_dilate {n : ℕ} (p : ℝ) (hp : 0 < p)
    {ρ : ℝ} (hρ : 0 < ρ) (K O : Set (Space n)) :
    relativeCapacity p (ρ • K) (ρ • O) =
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * relativeCapacity p K O := by
  apply le_antisymm (relativeCapacity_dilate_le p hp hρ K O)
  have hb := relativeCapacity_dilate_le p hp (inv_pos.mpr hρ) (ρ • K) (ρ • O)
  have hset (S : Set (Space n)) : ρ⁻¹ • (ρ • S) = S := by
    rw [smul_smul, inv_mul_cancel₀ hρ.ne', one_smul]
  rw [hset K,hset O,Real.inv_rpow hρ.le,
    ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hρ _)] at hb
  have hzero : ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ _))
  calc
    ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * relativeCapacity p K O ≤
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) *
        ((ENNReal.ofReal (ρ ^ ((n : ℝ) - p)))⁻¹ *
          relativeCapacity p (ρ • K) (ρ • O)) := mul_le_mul le_rfl hb zero_le zero_le
    _ = relativeCapacity p (ρ • K) (ρ • O) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hzero ENNReal.ofReal_ne_top, one_mul]

theorem relativeCapacity_translate_le {n : ℕ} (p : ℝ) (hp : 0 < p)
    (K O : Set (Space n)) (a : Space n) :
    relativeCapacity p (K + {a}) (O + {a}) ≤ relativeCapacity p K O := by
  unfold relativeCapacity
  refine le_iInf fun f => le_iInf fun hf => ?_
  have hd := hf.translateTest a
  apply (relativeCapacity_le_energy p hd).trans_eq
  rw [pEnergy_eq_univ_of_tsupport_subset p hp.ne' hd.2.2.1,
    pEnergy_translateTest p hp a hf.1 hf.2.1,
    pEnergy_eq_univ_of_tsupport_subset p hp.ne' hf.2.2.1]

theorem relativeCapacity_translate {n : ℕ} (p : ℝ) (hp : 0 < p)
    (K O : Set (Space n)) (a : Space n) :
    relativeCapacity p (K + {a}) (O + {a}) = relativeCapacity p K O := by
  apply le_antisymm (relativeCapacity_translate_le p hp K O a)
  have hb := relativeCapacity_translate_le p hp (K + {a}) (O + {a}) (-a)
  have hset (S : Set (Space n)) : (S + {a}) + {-a} = S := by
    simp only [add_assoc,singleton_add_singleton,add_neg_cancel,singleton_zero,add_zero]
  simpa only [hset] using hb

theorem relativeCapacity_affine {n : ℕ} (p : ℝ) (hp : 0 < p)
    {ρ : ℝ} (hρ : 0 < ρ) (K O : Set (Space n)) (a : Space n) :
    relativeCapacity p (ρ • K + {a}) (ρ • O + {a}) =
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * relativeCapacity p K O := by
  rw [relativeCapacity_translate p hp,relativeCapacity_dilate p hp hρ]

end BMCompactCapacityV2
#print axioms BMCompactCapacityV2.Admissible.dilateTest
#print axioms BMCompactCapacityV2.Admissible.translateTest
#print axioms BMCompactCapacityV2.relativeCapacity_dilate_le
#print axioms BMCompactCapacityV2.relativeCapacity_dilate
#print axioms BMCompactCapacityV2.relativeCapacity_translate_le
#print axioms BMCompactCapacityV2.relativeCapacity_translate
#print axioms BMCompactCapacityV2.relativeCapacity_affine
