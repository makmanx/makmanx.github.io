import CapacityNormalization

/-! Complete passage from the explicitly assumed minimum comparison to the
actual ENNReal capacity inequality, including zero-capacity and endpoint cases.
The minimum comparison itself remains an open nonlinear PDE obligation. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal Pointwise
namespace BMCompactCapacityV2

theorem ofReal_subcriticalCapacityRoot {n : ℕ} (p : ℝ) (hp : 0 < p)
    (hpn : p < (n : ℝ)) {K : Set (Space n)} (hK : IsCompact K) :
    ENNReal.ofReal (subcriticalCapacityRoot p K) =
      variationalCapacity p K ^ (1 / ((n : ℝ) - p)) := by
  exact ENNReal.ofReal_toReal (ENNReal.rpow_ne_top_of_nonneg
    (div_nonneg zero_le_one (sub_pos.mpr hpn).le)
    (variationalCapacity_ne_top_of_isCompact p hp hK))

theorem subcriticalCapacityRoot_mono {n : ℕ} (p : ℝ) (hp : 0 < p)
    (hpn : p < (n : ℝ)) {K L : Set (Space n)} (hL : IsCompact L) (hKL : K ⊆ L) :
    subcriticalCapacityRoot p K ≤ subcriticalCapacityRoot p L := by
  exact ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg
    (div_nonneg zero_le_one (sub_pos.mpr hpn).le)
    (variationalCapacity_ne_top_of_isCompact p hp hL))
    (ENNReal.rpow_le_rpow (variationalCapacity_mono p hKL)
      (div_nonneg zero_le_one (sub_pos.mpr hpn).le))

theorem weighted_capacityRoot_ge_left {n : ℕ} (p : ℝ) (hp : 0 < p)
    (hpn : p < (n : ℝ)) (E F : Set (Space n))
    (hE : IsCompact E) (hF : IsCompact F) (hFn : F.Nonempty)
    {t : ℝ} (ht : 0 < t) :
    t * subcriticalCapacityRoot p E ≤
      subcriticalCapacityRoot p (t • E + (1-t) • F) := by
  obtain ⟨y,hy⟩ := hFn
  have hsub : t • E + {(1-t) • y} ⊆ t • E + (1-t) • F := by
    rintro x ⟨a,ha,b,hb,rfl⟩
    have hb' := mem_singleton_iff.mp hb
    refine ⟨a,ha,b,?_,rfl⟩
    rw [hb']
    exact ⟨y,hy,rfl⟩
  have hm := subcriticalCapacityRoot_mono p hp hpn
    ((hE.smul t).add (hF.smul (1-t))) hsub
  rwa [subcriticalCapacityRoot_translate p hp,
    subcriticalCapacityRoot_dilate p hp hpn ht] at hm

theorem subcritical_BM_all_cases_of_min_comparison {n : ℕ} (p : ℝ) (hp : 0 < p)
    (hpn : p < (n : ℝ))
    (hmin : ∀ (K L : Set (Space n)), IsCompact K → IsCompact L →
      K.Nonempty → L.Nonempty → ∀ s : ℝ, 0 < s → s < 1 →
      min (subcriticalCapacityRoot p K) (subcriticalCapacityRoot p L) ≤
        subcriticalCapacityRoot p (s • K + (1-s) • L))
    (E F : Set (Space n)) (hE : IsCompact E) (hF : IsCompact F)
    (hEn : E.Nonempty) (hFn : F.Nonempty)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t * subcriticalCapacityRoot p E + (1-t) * subcriticalCapacityRoot p F ≤
      subcriticalCapacityRoot p (t • E + (1-t) • F) := by
  by_cases h0 : t = 0
  · subst t
    simp only [zero_mul,zero_smul_set hEn,sub_zero,one_mul,one_smul,zero_add]
    exact le_rfl
  by_cases h1 : t = 1
  · subst t
    simp only [one_mul,one_smul,sub_self,zero_mul,zero_smul_set hFn,add_zero]
    exact le_rfl
  have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm h0)
  have ht1' : t < 1 := lt_of_le_of_ne ht1 h1
  by_cases ha : 0 < subcriticalCapacityRoot p E
  · by_cases hb : 0 < subcriticalCapacityRoot p F
    · exact subcritical_BM_of_min_comparison p hp hpn hmin E F hE hF hEn hFn ha hb t ht' ht1'
    · have hb0 : subcriticalCapacityRoot p F = 0 :=
        le_antisymm (not_lt.mp hb) (subcriticalCapacityRoot_nonneg p F)
      simpa only [hb0,mul_zero,add_zero] using
        weighted_capacityRoot_ge_left p hp hpn E F hE hF hFn ht'
  · have ha0 : subcriticalCapacityRoot p E = 0 :=
      le_antisymm (not_lt.mp ha) (subcriticalCapacityRoot_nonneg p E)
    have hr := weighted_capacityRoot_ge_left p hp hpn F E hF hE hEn (sub_pos.mpr ht1')
    simpa only [ha0,mul_zero,zero_add,sub_sub_cancel,add_comm] using hr

/-- Exact capacity-root inequality of Theorem A(a), with the unresolved
minimum comparison stated visibly as a hypothesis. No main proof is claimed. -/
theorem subcritical_ENNReal_BM_of_min_comparison {n : ℕ} (p : ℝ) (hp : 0 < p)
    (hpn : p < (n : ℝ))
    (hmin : ∀ (K L : Set (Space n)), IsCompact K → IsCompact L →
      K.Nonempty → L.Nonempty → ∀ s : ℝ, 0 < s → s < 1 →
      min (subcriticalCapacityRoot p K) (subcriticalCapacityRoot p L) ≤
        subcriticalCapacityRoot p (s • K + (1-s) • L))
    (E F : Set (Space n)) (hE : IsCompact E) (hF : IsCompact F)
    (hEn : E.Nonempty) (hFn : F.Nonempty)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal t * variationalCapacity p E ^ (1 / ((n : ℝ) - p)) +
      ENNReal.ofReal (1-t) * variationalCapacity p F ^ (1 / ((n : ℝ) - p)) ≤
      variationalCapacity p (t • E + (1-t) • F) ^ (1 / ((n : ℝ) - p)) := by
  have hm := ENNReal.ofReal_le_ofReal
    (subcritical_BM_all_cases_of_min_comparison p hp hpn hmin E F hE hF hEn hFn t ht ht1)
  rwa [ENNReal.ofReal_add (mul_nonneg ht (subcriticalCapacityRoot_nonneg p E))
      (mul_nonneg (sub_nonneg.mpr ht1) (subcriticalCapacityRoot_nonneg p F)),
    ENNReal.ofReal_mul ht,ENNReal.ofReal_mul (sub_nonneg.mpr ht1),
    ofReal_subcriticalCapacityRoot p hp hpn hE,
    ofReal_subcriticalCapacityRoot p hp hpn hF,
    ofReal_subcriticalCapacityRoot p hp hpn ((hE.smul t).add (hF.smul (1-t)))] at hm

end BMCompactCapacityV2
#print axioms BMCompactCapacityV2.ofReal_subcriticalCapacityRoot
#print axioms BMCompactCapacityV2.subcriticalCapacityRoot_mono
#print axioms BMCompactCapacityV2.weighted_capacityRoot_ge_left
#print axioms BMCompactCapacityV2.subcritical_BM_all_cases_of_min_comparison
#print axioms BMCompactCapacityV2.subcritical_ENNReal_BM_of_min_comparison
