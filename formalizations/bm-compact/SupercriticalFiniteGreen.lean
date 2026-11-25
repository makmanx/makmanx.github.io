import GreenWeakReflection
import SupercriticalGreenSeparatedLimit
import FiniteGreenSimilarity
import FillMinkowski

noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology Pointwise
namespace BMCompactPDE

/-- For every supercritical Green function the bounded remainder has one finite limit.
No differentiability or quantitative angular decay is an assumption. -/
theorem IsExteriorGreen.existsUnique_finite_supercritical_asymptotic
    {n : ℕ} {p σ : ℝ} {K : Set (Space n)} {G : Space n → ℝ}
    (hG : IsExteriorGreen n σ p K G) (hnp : (n:ℝ)<p) :
    ∃! k : ℝ, HasGreenAsymptotic n σ p G k :=
  hG.existsUnique_finite_supercritical_asymptotic_of_separated_order hnp hG.separated_order

theorem existsUnique_canonical_supercritical_green_capacity {n : ℕ} {p : ℝ}
    (hn : 2≤n) (hnp : (n:ℝ)<p) {K : Set (Space n)} (hK : IsCompact K) (hk : K.Nonempty) :
    ∃! c : ℝ, HasFiniteGreenCapacity (canonicalSphereArea n) p K c := by
  obtain ⟨G,_,hG,_⟩ := exists_canonical_exterior_green_supercritical_nonempty hn hnp hK hk
  obtain ⟨k,hl,_⟩ := hG.existsUnique_finite_supercritical_asymptotic hnp
  have h : HasFiniteGreenCapacity (canonicalSphereArea n) p K
      (greenCapacityOfConstant n (canonicalSphereArea n) p k) := ⟨G,k,hG,hl,rfl⟩
  exact ⟨_,h,fun _ hd=>hd.unique h⟩

/-- The manuscript's finite supercritical Green capacity. The preceding theorem
ensures a unique value for each nonempty compact in the stated range. -/
def canonicalSupercriticalGreenCapacity {n : ℕ} (p : ℝ) (K : Set (Space n)) : ℝ :=
  sInf {c : ℝ | HasFiniteGreenCapacity (canonicalSphereArea n) p K c}

private theorem supercritical_value_of_witness {n : ℕ} {p c : ℝ} {K : Set (Space n)}
    (hc : HasFiniteGreenCapacity (canonicalSphereArea n) p K c) : canonicalSupercriticalGreenCapacity p K=c := by
  have he : {d : ℝ | HasFiniteGreenCapacity (canonicalSphereArea n) p K d}={c} := by
    ext d; exact ⟨fun hd=>hd.unique hc,fun hd=>by obtain rfl : d=c := hd; exact hc⟩
  rw [canonicalSupercriticalGreenCapacity,he,csInf_singleton]

theorem has_canonical_supercritical_green_capacity {n : ℕ} {p : ℝ}
    (hn : 2≤n) (hnp : (n:ℝ)<p) {K : Set (Space n)} (hK : IsCompact K) (hk : K.Nonempty) :
    HasFiniteGreenCapacity (canonicalSphereArea n) p K (canonicalSupercriticalGreenCapacity p K) := by
  obtain ⟨c,hc,_⟩ := existsUnique_canonical_supercritical_green_capacity hn hnp hK hk
  rwa [supercritical_value_of_witness hc]

theorem canonicalSupercriticalGreenCapacity_mono {n : ℕ} {p : ℝ}
    (hn : 2≤n) (hnp : (n:ℝ)<p) {K L : Set (Space n)} (hK : IsCompact K) (hL : IsCompact L)
    (hk : K.Nonempty) (hkl : K⊆L) : canonicalSupercriticalGreenCapacity p K≤canonicalSupercriticalGreenCapacity p L := by
  obtain ⟨G,k,hG,hk',he⟩ := has_canonical_supercritical_green_capacity hn hnp hK hk
  obtain ⟨H,l,hH,hl',he'⟩ := has_canonical_supercritical_green_capacity hn hnp hL (hk.mono hkl)
  rw [he,he']
  simp only [greenCapacityOfConstant,if_neg hnp.ne']
  exact Real.rpow_le_rpow (neg_nonneg.mpr (hG.supercritical_constant_nonpos hnp hk'))
    (neg_le_neg (hG.asymptotic_constant_antitone_obstacle hH hkl hk' hl'))
    (sub_pos.mpr (hG.1.trans hnp)).le

theorem canonicalSupercriticalGreenCapacity_similarity {n : ℕ} {p : ℝ}
    (hn : 2≤n) (hnp : (n:ℝ)<p) {K : Set (Space n)} (hK : IsCompact K) (hk : K.Nonempty)
    {ρ : ℝ} (hρ : 0<ρ) (a : Space n) :
    canonicalSupercriticalGreenCapacity p (ρ • K+{a})=ρ^(p-n)*canonicalSupercriticalGreenCapacity p K :=
  supercritical_value_of_witness (((has_canonical_supercritical_green_capacity hn hnp hK hk).dilate_supercritical hnp hρ).translate a)

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.existsUnique_finite_supercritical_asymptotic
#print axioms BMCompactPDE.existsUnique_canonical_supercritical_green_capacity
#print axioms BMCompactPDE.has_canonical_supercritical_green_capacity
#print axioms BMCompactPDE.canonicalSupercriticalGreenCapacity_mono
#print axioms BMCompactPDE.canonicalSupercriticalGreenCapacity_similarity
