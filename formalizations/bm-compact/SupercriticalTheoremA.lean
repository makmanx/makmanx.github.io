import SupercriticalFiniteGreen
import SupercriticalFilledEquality

noncomputable section
set_option autoImplicit false
open Set
open scoped Pointwise
namespace BMCompactPDE

theorem canonicalSupercriticalGreenCapacity_nonneg {n : ℕ} {p : ℝ} {K : Set (Space n)}
    (hn : 2 ≤ n) (hnp : (n:ℝ)<p) (hK : IsCompact K) (hk : K.Nonempty) :
    0 ≤ canonicalSupercriticalGreenCapacity p K := by
  obtain ⟨G,k,hG,hl,he⟩ := has_canonical_supercritical_green_capacity hn hnp hK hk
  rw [he,greenCapacityOfConstant,if_neg hnp.ne']
  exact Real.rpow_nonneg (neg_nonneg.mpr (hG.supercritical_constant_nonpos hnp hl)) _

/-- A(c) for any compact set paired with a translate and positive dilate
of itself. No convexity or positivity of its capacity is required. -/
theorem theoremA_supercritical_homothetic {n : ℕ} {p : ℝ} (hn : 2≤n) (hnp : (n:ℝ)<p)
    {K : Set (Space n)} (hK : IsCompact K) (hk : K.Nonempty) {t ρ : ℝ}
    (ht : 0≤t) (ht1 : t≤1) (hρ : 0<ρ) (a : Space n) :
    t*canonicalSupercriticalGreenCapacity p K^(1/(p-n)) +
        (1-t)*canonicalSupercriticalGreenCapacity p (ρ • K+{a})^(1/(p-n)) ≤
      canonicalSupercriticalGreenCapacity p (t • K+(1-t) • (ρ • K+{a}))^(1/(p-n)) := by
  let b := t+(1-t)*ρ
  have hb : 0<b := by
    rcases eq_or_lt_of_le ht with e|h
    · subst t;simpa [b] using hρ
    · exact add_pos_of_pos_of_nonneg h (mul_nonneg (sub_nonneg.mpr ht1) hρ.le)
  have hsub : b • K+{(1-t) • a} ⊆ t • K+(1-t) • (ρ • K+{a}) := by
    rw [smul_add,smul_smul,smul_set_singleton,←add_assoc]
    exact add_subset_add_right (add_smul_subset t ((1-t)*ρ) K)
  have hmono := canonicalSupercriticalGreenCapacity_mono hn hnp
    ((hK.smul b).add isCompact_singleton) ((hK.smul t).add (((hK.smul ρ).add isCompact_singleton).smul _))
    ((hk.image _).add (singleton_nonempty _)) hsub
  have h := Real.rpow_le_rpow (canonicalSupercriticalGreenCapacity_nonneg hn hnp
    ((hK.smul b).add isCompact_singleton) ((hk.image _).add (singleton_nonempty _))) hmono
    (one_div_pos.mpr (sub_pos.mpr hnp)).le
  have scale {s : ℝ} (hs : 0<s) (v : Space n) :
      canonicalSupercriticalGreenCapacity p (s • K+{v})^(1/(p-n)) =
        s*canonicalSupercriticalGreenCapacity p K^(1/(p-n)) := by
    rw [canonicalSupercriticalGreenCapacity_similarity hn hnp hK hk hs,
      Real.mul_rpow (Real.rpow_nonneg hs.le _) (canonicalSupercriticalGreenCapacity_nonneg hn hnp hK hk),
      ←Real.rpow_mul hs.le,show (p-(n:ℝ))*(1/(p-n))=1 by field_simp [(sub_pos.mpr hnp).ne'],
      Real.rpow_one]
  rw [scale hb] at h
  rw [scale hρ]
  simpa only [b,add_mul,mul_assoc] using h

/-- The sufficient direction of A(d), in the supercritical normalization of
the paper. Existence of the three finite capacities follows from compactness. -/
theorem theoremA_supercritical_filled_equality {n : ℕ} {p : ℝ}
    (hn : 2≤n) (hnp : (n:ℝ)<p) {K L : Set (Space n)} (hK : IsCompact K)
    (hL : IsCompact L) (hk : K.Nonempty) (hl : L.Nonempty)
    (hpos : 0 < canonicalSupercriticalGreenCapacity p K ^ (1/(p-n)))
    (hconv : Convex ℝ (fillBoundedHoles K)) (a : Space n) {ρ t : ℝ} (hρ : 0<ρ)
    (heq : fillBoundedHoles L = ρ • fillBoundedHoles K + {a}) (ht : 0<t) (ht1 : t<1) :
    canonicalSupercriticalGreenCapacity p (t • K+(1-t) • L) ^ (1/(p-n)) =
      t * canonicalSupercriticalGreenCapacity p K ^ (1/(p-n)) +
        (1-t) * canonicalSupercriticalGreenCapacity p L ^ (1/(p-n)) := by
  have hc := has_canonical_supercritical_green_capacity hn hnp hK hk
  have hp : 0 < canonicalSupercriticalGreenCapacity p K := by
    rcases eq_or_lt_of_le (canonicalSupercriticalGreenCapacity_nonneg hn hnp hK hk) with hz | hp
    · rw [←hz,Real.zero_rpow (one_div_pos.mpr (sub_pos.mpr hnp)).ne'] at hpos
      exact (lt_irrefl _ hpos).elim
    · exact hp
  obtain ⟨d,e,hd,he,hm⟩ := theoremA_supercritical_equality_of_filled_convex_homothetic
    hn hnp hK hL hk hl hc hp hconv a hρ heq ht ht1
  rw [hd.unique (has_canonical_supercritical_green_capacity hn hnp hL hl),
    he.unique (has_canonical_supercritical_green_capacity hn hnp
      ((hK.smul t).add (hL.smul (1-t))) ((hk.image _).add (hl.image _)))] at hm
  exact hm

end BMCompactPDE
#print axioms BMCompactPDE.canonicalSupercriticalGreenCapacity_nonneg
#print axioms BMCompactPDE.theoremA_supercritical_homothetic
#print axioms BMCompactPDE.theoremA_supercritical_filled_equality
