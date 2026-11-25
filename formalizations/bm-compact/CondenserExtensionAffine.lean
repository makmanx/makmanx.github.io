import CondenserExtension
import RelativeCapacityAffine
import Mathlib.Topology.Homeomorph.Lemmas

/-!
Affine covariance of the exact inner/outer condenser extension, source
eqn9.1(c). The homeomorphism transport proof is applied to the actual proved
variational affine law. This concerns condenser capacity, not Green capacity.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal Pointwise

namespace BMCompactCapacityV2

theorem outerCondenserCapacity_eq_inner_of_isOpen {n : ℕ} (p : ℝ)
    {U O : Set (Space n)} (hU : IsOpen U) (hUO : U ⊆ O) :
    outerCondenserCapacity p U O = innerCondenserCapacity p U O := by
  apply le_antisymm (outerCondenserCapacity_le_inner p hU Subset.rfl hUO)
  refine le_iInf fun W => le_iInf fun _ => le_iInf fun hUW => le_iInf fun _ => ?_
  exact innerCondenserCapacity_mono p hUW

theorem innerCondenserCapacity_image {n : ℕ} (p : ℝ)
    (h : Space n ≃ₜ Space n) (c : ℝ≥0∞) (O : Set (Space n))
    (hcap : ∀ K : Set (Space n),
      relativeCapacity p (h '' K) (h '' O) = c * relativeCapacity p K O)
    (U : Set (Space n)) :
    innerCondenserCapacity p (h '' U) (h '' O) = c * innerCondenserCapacity p U O := by
  apply le_antisymm
  · refine iSup_le fun K => iSup_le fun hK => iSup_le fun hKU => ?_
    have hpreK : IsCompact (h ⁻¹' K) := h.isCompact_preimage.mpr hK
    have hpreU : h ⁻¹' K ⊆ U := by
      simpa only [h.preimage_image] using (preimage_mono hKU : h ⁻¹' K ⊆ h ⁻¹' (h '' U))
    calc
      relativeCapacity p K (h '' O) = c * relativeCapacity p (h ⁻¹' K) O := by
        simpa only [h.image_preimage] using hcap (h ⁻¹' K)
      _ ≤ c * innerCondenserCapacity p U O :=
        mul_le_mul le_rfl (relativeCapacity_le_innerCondenserCapacity p hpreK hpreU)
          zero_le zero_le
  · rw [innerCondenserCapacity, ENNReal.mul_iSup]
    refine iSup_le fun K => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hK => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hKU => ?_
    rw [← hcap K]
    exact relativeCapacity_le_innerCondenserCapacity p (hK.image h.continuous) (image_mono hKU)

theorem outerCondenserCapacity_image {n : ℕ} (p : ℝ)
    (h : Space n ≃ₜ Space n) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (O : Set (Space n))
    (hcap : ∀ K : Set (Space n),
      relativeCapacity p (h '' K) (h '' O) = c * relativeCapacity p K O)
    (A : Set (Space n)) :
    outerCondenserCapacity p (h '' A) (h '' O) = c * outerCondenserCapacity p A O := by
  have hin := innerCondenserCapacity_image p h c O hcap
  apply le_antisymm
  · change outerCondenserCapacity p (h '' A) (h '' O) ≤
      c * (⨅ (U : Set (Space n)) (_ : IsOpen U) (_ : A ⊆ U) (_ : U ⊆ O),
        innerCondenserCapacity p U O)
    rw [ENNReal.mul_iInf_of_ne hc0 hct]
    refine le_iInf fun U => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 hct]
    refine le_iInf fun hU => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 hct]
    refine le_iInf fun hAU => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 hct]
    refine le_iInf fun hUO => ?_
    exact (outerCondenserCapacity_le_inner p (h.isOpen_image.mpr hU)
      (image_mono hAU) (image_mono hUO)).trans_eq (hin U)
  · refine le_iInf fun U => le_iInf fun hU => le_iInf fun hAU => le_iInf fun hUO => ?_
    have hpreA : A ⊆ h ⁻¹' U := by
      intro x hx
      exact hAU ⟨x,hx,rfl⟩
    have hpreO : h ⁻¹' U ⊆ O := by
      simpa only [h.preimage_image] using (preimage_mono hUO : h ⁻¹' U ⊆ h ⁻¹' (h '' O))
    calc
      c * outerCondenserCapacity p A O ≤ c * innerCondenserCapacity p (h ⁻¹' U) O :=
        mul_le_mul le_rfl (outerCondenserCapacity_le_inner p (h.isOpen_preimage.mpr hU)
          hpreA hpreO) zero_le zero_le
      _ = innerCondenserCapacity p U (h '' O) := by
        simpa only [h.image_preimage] using (hin (h ⁻¹' U)).symm

def condenserAffineHomeomorph {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (a : Space n) :
    Space n ≃ₜ Space n :=
  (Homeomorph.smul (Units.mk0 ρ hρ.ne')).trans (Homeomorph.addRight a)

theorem condenserAffineHomeomorph_image {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (a : Space n) (S : Set (Space n)) :
    condenserAffineHomeomorph hρ a '' S = ρ • S + {a} := by
  have hp (x : Space n) : condenserAffineHomeomorph hρ a x = ρ • x + a := rfl
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨ρ • y,⟨y,hy,rfl⟩,a,mem_singleton a,(hp y).symm⟩
  · rintro ⟨r,⟨y,hy,rfl⟩,z,hz,rfl⟩
    refine ⟨y,hy,?_⟩
    rw [hp,mem_singleton_iff.mp hz]

theorem innerCondenserCapacity_affine {n : ℕ} (p : ℝ) (hp : 0 < p)
    {ρ : ℝ} (hρ : 0 < ρ) (U O : Set (Space n)) (a : Space n) :
    innerCondenserCapacity p (ρ • U + {a}) (ρ • O + {a}) =
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * innerCondenserCapacity p U O := by
  have hcap : ∀ K : Set (Space n), relativeCapacity p
      (condenserAffineHomeomorph hρ a '' K) (condenserAffineHomeomorph hρ a '' O) =
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * relativeCapacity p K O := by
    intro K
    rw [condenserAffineHomeomorph_image,condenserAffineHomeomorph_image]
    exact relativeCapacity_affine p hp hρ K O a
  simpa only [condenserAffineHomeomorph_image] using
    innerCondenserCapacity_image p (condenserAffineHomeomorph hρ a) _ O hcap U

/-- The manuscript's extended condenser affine law, with both the inner
set and open domain moved. No compactness of the inner set is assumed. -/
theorem outerCondenserCapacity_affine {n : ℕ} (p : ℝ) (hp : 0 < p)
    {ρ : ℝ} (hρ : 0 < ρ) (A O : Set (Space n)) (a : Space n) :
    outerCondenserCapacity p (ρ • A + {a}) (ρ • O + {a}) =
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * outerCondenserCapacity p A O := by
  have hcap : ∀ K : Set (Space n), relativeCapacity p
      (condenserAffineHomeomorph hρ a '' K) (condenserAffineHomeomorph hρ a '' O) =
      ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) * relativeCapacity p K O := by
    intro K
    rw [condenserAffineHomeomorph_image,condenserAffineHomeomorph_image]
    exact relativeCapacity_affine p hp hρ K O a
  have hc0 : ENNReal.ofReal (ρ ^ ((n : ℝ) - p)) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hρ _))
  simpa only [condenserAffineHomeomorph_image] using
    outerCondenserCapacity_image p (condenserAffineHomeomorph hρ a) _ hc0
      ENNReal.ofReal_ne_top O hcap A

end BMCompactCapacityV2

#print axioms BMCompactCapacityV2.innerCondenserCapacity_image
#print axioms BMCompactCapacityV2.outerCondenserCapacity_eq_inner_of_isOpen
#print axioms BMCompactCapacityV2.outerCondenserCapacity_image
#print axioms BMCompactCapacityV2.condenserAffineHomeomorph_image
#print axioms BMCompactCapacityV2.innerCondenserCapacity_affine
#print axioms BMCompactCapacityV2.outerCondenserCapacity_affine
