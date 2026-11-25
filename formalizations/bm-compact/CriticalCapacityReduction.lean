import CanonicalCriticalOuterCapacity
import CapacityNormalization
import FillMinkowski
import CriticalOuterBallCase

noncomputable section
set_option autoImplicit false
open Set Filter Metric Bornology
open scoped Topology Pointwise
namespace BMCompactPDE

/-- Pointwise maximum comparison on ordinary Green functions of the
neighborhoods, the remaining nonlinear input in Theorem B(c). -/
def HasCriticalNeighborhoodComparison (n : ℕ) : Prop :=
  ∀ {K L : Set (Space n)}, IsCompact K → IsCompact L → K.Nonempty → L.Nonempty →
  ∀ {t : ℝ}, 0 < t → t < 1 → ∀ {δ : ℝ}, 0 < δ → ∀ {G H J : Space n → ℝ},
    IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood δ K) G →
    IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood δ L) H →
    IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood δ (t • K+(1-t) • L)) J →
    ∀ y z, J (t • y+(1-t) • z) ≤ max (G y) (H z)

theorem canonicalCriticalOuterCapacity_nonneg {n : ℕ} (hn : 2 ≤ n) {K : Set (Space n)}
    (hK : IsCompact K) (hk : K.Nonempty) : 0 ≤ canonicalCriticalOuterCapacity K := by
  obtain ⟨c,hc,hl⟩ := has_canonical_critical_outer_capacity hn hK hk
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hl
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hc r hr).pos.le

private theorem min_critical_outer_of_comparison {n : ℕ} (hn : 2 ≤ n)
    (hcmp : HasCriticalNeighborhoodComparison n) {K L : Set (Space n)}
    (hK : IsCompact K) (hL : IsCompact L) (hk : K.Nonempty) (hl : L.Nonempty)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) : min (canonicalCriticalOuterCapacity K)
      (canonicalCriticalOuterCapacity L) ≤ canonicalCriticalOuterCapacity (t • K+(1-t) • L) := by
  let _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let M := t • K+(1-t) • L
  obtain ⟨c,hc,lc⟩ := has_canonical_critical_outer_capacity hn hK hk
  obtain ⟨d,hd,ld⟩ := has_canonical_critical_outer_capacity hn hL hl
  obtain ⟨e,he,le'⟩ := has_canonical_critical_outer_capacity hn ((hK.smul t).add (hL.smul (1-t)))
    ((hk.image _).add (hl.image _))
  apply le_of_tendsto_of_tendsto (lc.min ld) le'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  obtain ⟨G,k,hG,hk',hc'⟩ := hc δ hδ
  obtain ⟨H,l,hH,hl',hd'⟩ := hd δ hδ
  obtain ⟨J,m,hJ,hm',he'⟩ := he δ hδ
  have h := hcmp hK hL hk hl ht ht1 hδ hG hH hJ
  have hkl : m ≤ max k l := le_of_tendsto_of_tendsto' hm' (hk'.max hl') (fun x => by
    change J x - fundamentalPotential n _ _ x ≤ max (G x - _) (H x - _)
    rw [max_sub_sub_right]
    apply sub_le_sub_right
    have heq : t • x+(1-t) • x = x := by rw [← add_smul,add_sub_cancel,one_smul]
    simpa only [heq] using h x x)
  rw [hc',hd',he']
  simp only [greenCapacityOfConstant,ite_true]
  let γ := (canonicalSphereArea n)^(-((n:ℝ)-1)⁻¹)
  have hγ : 0 ≤ γ := Real.rpow_nonneg (canonicalSphereArea_pos (by omega)).le _
  have anti (a b : ℝ) (h : a ≤ b) : Real.exp (-b/γ) ≤ Real.exp (-a/γ) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg h) hγ)
  rcases le_total k l with h | h
  · rw [max_eq_right h] at hkl
    exact (min_le_right _ _).trans (anti m l hkl)
  · rw [max_eq_left h] at hkl
    exact (min_le_left _ _).trans (anti m k hkl)

private theorem canonicalCriticalOuterCapacity_dilate {n : ℕ} (hn : 2 ≤ n) {K : Set (Space n)}
    (hK : IsCompact K) (hk : K.Nonempty) {ρ : ℝ} (hρ : 0<ρ) :
    canonicalCriticalOuterCapacity (ρ • K) = ρ*canonicalCriticalOuterCapacity K := by
  simpa using canonical_critical_outer_capacity_affine hn hK hk hρ 0

private theorem critical_weighted_ge_left {n : ℕ} (hn : 2 ≤ n) {K L : Set (Space n)}
    (hK : IsCompact K) (hL : IsCompact L) (hk : K.Nonempty) (hl : L.Nonempty)
    {t : ℝ} (ht : 0 < t) : t*canonicalCriticalOuterCapacity K ≤
      canonicalCriticalOuterCapacity (t • K+(1-t) • L) := by
  obtain ⟨y,hy⟩ := hl
  have hsub : t • K + {(1-t) • y} ⊆ t • K + (1-t) • L := by
    rintro _ ⟨z,hz,w,hw,rfl⟩
    obtain rfl : w = (1-t) • y := hw
    exact ⟨z,hz,_,⟨y,hy,rfl⟩,rfl⟩
  rw [← canonical_critical_outer_capacity_affine hn hK hk ht ((1-t) • y)]
  exact canonical_critical_outer_capacity_mono hn ((hK.smul t).add isCompact_singleton)
    ((hK.smul t).add (hL.smul (1-t))) ((hk.image _).add (singleton_nonempty _)) hsub

theorem theoremB_critical_of_neighborhood_comparison {n : ℕ} (hn : 2 ≤ n)
    (hcmp : HasCriticalNeighborhoodComparison n) {E F : Set (Space n)}
    (hE : IsCompact E) (hF : IsCompact F) (he : E.Nonempty) (hf : F.Nonempty)
    {t : ℝ} (ht : 0≤t) (ht1 : t≤1) : t*canonicalCriticalOuterCapacity E +
      (1-t)*canonicalCriticalOuterCapacity F ≤ canonicalCriticalOuterCapacity (t • E+(1-t) • F) := by
  rcases eq_or_lt_of_le ht with ht | ht
  · subst t; simp [zero_smul_set he]
  rcases eq_or_lt_of_le ht1 with ht1 | ht1
  · subst t; simp [zero_smul_set hf]
  let a := canonicalCriticalOuterCapacity E
  let b := canonicalCriticalOuterCapacity F
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · let A := BMCompact.normalizationScale t a b
      let s := BMCompact.normalizationWeight t a b
      have hA := BMCompact.normalizationScale_pos ht ht1 ha hb
      have hsl := BMCompact.normalizationWeight_pos ht ht1 ha hb
      have hsr := BMCompact.normalizationWeight_lt_one ht ht1 ha hb
      have hm := min_critical_outer_of_comparison hn hcmp (hE.smul a⁻¹) (hF.smul b⁻¹)
        (he.image _) (hf.image _) hsl hsr
      rw [canonicalCriticalOuterCapacity_dilate hn hE he (inv_pos.mpr ha),
        canonicalCriticalOuterCapacity_dilate hn hF hf (inv_pos.mpr hb)] at hm
      change min (a⁻¹*a) (b⁻¹*b) ≤ _ at hm
      rw [inv_mul_cancel₀ ha.ne',inv_mul_cancel₀ hb.ne',min_self,
        BMCompactCapacityV2.normalization_pointwise_set_identity ht ht1 ha hb E F,
        canonicalCriticalOuterCapacity_dilate hn ((hE.smul t).add (hF.smul (1-t)))
          ((he.image _).add (hf.image _)) (inv_pos.mpr hA)] at hm
      have hh := mul_le_mul_of_nonneg_left hm hA.le
      rw [mul_one,←mul_assoc,mul_inv_cancel₀ hA.ne',one_mul] at hh
      exact hh
    · have hz : canonicalCriticalOuterCapacity F = 0 :=
        le_antisymm (le_of_not_gt hb) (canonicalCriticalOuterCapacity_nonneg hn hF hf)
      simpa only [hz,mul_zero,add_zero] using (show t*canonicalCriticalOuterCapacity E +
        (1-t)*canonicalCriticalOuterCapacity F ≤ _ by rw [hz,mul_zero,add_zero];exact critical_weighted_ge_left hn hE hF he hf ht)
  · have hz : canonicalCriticalOuterCapacity E = 0 :=
      le_antisymm (le_of_not_gt ha) (canonicalCriticalOuterCapacity_nonneg hn hE he)
    rw [hz,mul_zero,zero_add]
    simpa only [sub_sub_cancel,add_comm] using critical_weighted_ge_left hn hF hE hf he (sub_pos.mpr ht1)

end BMCompactPDE
#print axioms BMCompactPDE.canonicalCriticalOuterCapacity_nonneg
#print axioms BMCompactPDE.theoremB_critical_of_neighborhood_comparison
