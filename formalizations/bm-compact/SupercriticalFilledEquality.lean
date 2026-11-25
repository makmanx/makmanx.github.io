import FiniteGreenSimilarity
import FillMinkowski

noncomputable section
set_option autoImplicit false
open Set
open scoped Topology Pointwise
namespace BMCompactPDE

theorem fillBoundedHoles_similarity {n : ℕ} {K : Set (Space n)} {ρ : ℝ}
    (hρ : ρ ≠ 0) (a : Space n) :
    fillBoundedHoles (ρ • K + {a}) = ρ • fillBoundedHoles K + {a} := by
  have hf : MapsTo (fun x : Space n=>ρ • x+a) K (ρ • K+{a}) :=
    fun x hx=>⟨_,⟨x,hx,rfl⟩,a,rfl,rfl⟩
  have hi : MapsTo (fun y : Space n=>ρ⁻¹ • y + -(ρ⁻¹ • a)) (ρ • K+{a}) K := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,z,hz,rfl⟩
    obtain rfl : z=a := hz
    simpa [smul_add,smul_smul,hρ] using hx
  ext y
  constructor
  · intro hy
    have h := affine_mapsTo_filled (inv_ne_zero hρ) _ hi hy
    refine ⟨_,⟨_,h,rfl⟩,a,rfl,?_⟩
    simp [smul_add,smul_neg,smul_smul,hρ]
  · rintro ⟨_,⟨x,hx,rfl⟩,z,hz,rfl⟩
    obtain rfl : z=a := hz
    exact affine_mapsTo_filled hρ _ hf hx

theorem fillBoundedHoles_mix_homothetic {n : ℕ} (hn : 2≤n) {K L : Set (Space n)}
    (hK : IsCompact K) (hL : IsCompact L) (hk : K.Nonempty) (hl : L.Nonempty)
    (hconv : Convex ℝ (fillBoundedHoles K)) {ρ t : ℝ} (hρ : 0<ρ) (a : Space n)
    (heq : fillBoundedHoles L = ρ • fillBoundedHoles K+{a}) (ht : 0<t) (ht1 : t<1) :
    fillBoundedHoles (t • K+(1-t) • L) = (t+(1-t)*ρ) • fillBoundedHoles K + {(1-t) • a} := by
  have hs := sub_pos.mpr ht1
  have hσ := add_pos ht (mul_pos hs hρ)
  have he : t • fillBoundedHoles K+(1-t) • fillBoundedHoles L =
      (t+(1-t)*ρ) • fillBoundedHoles K+{(1-t) • a} := by
    rw [heq,smul_add,smul_smul,smul_set_singleton,←add_assoc,←hconv.add_smul ht.le (mul_pos hs hρ).le]
  apply le_antisymm _ (he ▸ smul_fill_add_smul_fill_subset hn hK hL hk hl ht ht1)
  have hsub : t • K+(1-t) • L ⊆ t • fillBoundedHoles K+(1-t) • fillBoundedHoles L := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,_,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨_,⟨x,Or.inl hx,rfl⟩,_,⟨z,Or.inl hz,rfl⟩,rfl⟩
  rw [he] at hsub
  have h := fillBoundedHoles_mono hsub
  rwa [fillBoundedHoles_similarity hσ.ne', fillBoundedHoles_idempotent hn hK hk] at h

private theorem finite_capacity_of_filled {n : ℕ} {p c : ℝ} (hn : 2≤n) (hpn : (n:ℝ)<p)
    {K : Set (Space n)} (hK : IsCompact K) (hk : K.Nonempty)
    (hc : HasFiniteGreenCapacity (canonicalSphereArea n) p (fillBoundedHoles K) c) :
    HasFiniteGreenCapacity (canonicalSphereArea n) p K c := by
  obtain ⟨G,_,hG,_⟩ := exists_canonical_exterior_green_supercritical_nonempty hn hpn hK hk
  obtain ⟨H,k,hH,hk',he⟩ := hc
  rw [hH.unique hG.on_filled] at hk'
  exact ⟨G,k,hG,hk',he⟩

/-- Supercritical sufficiency in A(d) with the actual positive input Green capacity.
The normalized capacity of the second compact and the mixed compact are constructed. -/
theorem theoremA_supercritical_equality_of_filled_convex_homothetic {n : ℕ} {p c : ℝ}
    (hn : 2≤n) (hpn : (n:ℝ)<p) {K L : Set (Space n)} (hK : IsCompact K) (hL : IsCompact L)
    (hk : K.Nonempty) (hl : L.Nonempty) (hc : HasFiniteGreenCapacity (canonicalSphereArea n) p K c)
    (hcpos : 0<c) (hconv : Convex ℝ (fillBoundedHoles K)) (a : Space n) {ρ t : ℝ} (hρ : 0<ρ)
    (heq : fillBoundedHoles L=ρ • fillBoundedHoles K+{a}) (ht : 0<t) (ht1 : t<1) :
    ∃ d e : ℝ, HasFiniteGreenCapacity (canonicalSphereArea n) p L d ∧
      HasFiniteGreenCapacity (canonicalSphereArea n) p (t • K+(1-t) • L) e ∧
      e^(1/(p-n))=t*c^(1/(p-n))+(1-t)*d^(1/(p-n)) := by
  have hcf : HasFiniteGreenCapacity (canonicalSphereArea n) p (fillBoundedHoles K) c := by
    obtain ⟨G,k,hG,hk',he⟩ := hc;exact ⟨G,k,hG.on_filled,hk',he⟩
  have hs := sub_pos.mpr ht1
  have hm := add_pos ht (mul_pos hs hρ)
  have hl' := (hcf.dilate_supercritical hpn hρ).translate a
  rw [←heq] at hl'
  have hm' := (hcf.dilate_supercritical hpn hm).translate ((1-t) • a)
  rw [← fillBoundedHoles_mix_homothetic hn hK hL hk hl hconv hρ a heq ht ht1] at hm'
  refine ⟨_,_,finite_capacity_of_filled hn hpn hL hl hl',finite_capacity_of_filled hn hpn
    ((hK.smul t).add (hL.smul _)) ((hk.image _).add (hl.image _)) hm',?_⟩
  have hroot (b : ℝ) (hb : 0<b) :
      (b^(p-n)*c)^(1/(p-n))=b*c^(1/(p-n)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hb.le _) hcpos.le,←Real.rpow_mul hb.le,
      show (p-(n:ℝ))*(1/(p-n))=1 by field_simp [(sub_pos.mpr hpn).ne'],Real.rpow_one]
  rw [hroot _ hm,hroot _ hρ]
  ring

end BMCompactPDE
#print axioms BMCompactPDE.fillBoundedHoles_similarity
#print axioms BMCompactPDE.fillBoundedHoles_mix_homothetic
#print axioms BMCompactPDE.theoremA_supercritical_equality_of_filled_convex_homothetic
