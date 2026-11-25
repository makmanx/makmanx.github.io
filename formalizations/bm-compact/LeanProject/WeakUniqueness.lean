import WeakPDE
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Uniqueness of the actual distributional gradient, proved from smooth test
functions and the fundamental lemma of distributions. No PDE uniqueness or
comparison principle is assumed here.
-/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace BMCompactPDE

theorem HasWeakGradientOn.ae_unique {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g h : Space n → Space n}
    (hg : HasWeakGradientOn Ω u g) (hh : HasWeakGradientOn Ω u h)
    (hΩ : IsOpen Ω) (hgli : LocallyIntegrableOn g Ω volume)
    (hhli : LocallyIntegrableOn h Ω volume) :
    g =ᵐ[volume.restrict Ω] h := by
  have hcoord (i : Fin n) : ∀ᵐ x ∂volume, x ∈ Ω → (g x) i - (h x) i = 0 := by
    have hgi : LocallyIntegrableOn (fun x => (g x) i) Ω volume :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).locallyIntegrableOn_comp hgli
    have hhi : LocallyIntegrableOn (fun x => (h x) i) Ω volume :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).locallyIntegrableOn_comp hhli
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hgi.sub hhi)
    intro φ hφ hφc hφΩ
    obtain ⟨_, hgp, hgeq⟩ := hg φ ⟨hφ, hφc, hφΩ⟩ i
    obtain ⟨_, hhp, hheq⟩ := hh φ ⟨hφ, hφc, hφΩ⟩ i
    have heq : (∫ x in Ω, (g x) i * φ x) = (∫ x in Ω, (h x) i * φ x) := by
      linarith
    have hsupp : ∀ x, x ∉ Ω → φ x * ((g x) i - (h x) i) = 0 := by
      intro x hx
      have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun hxφ => hx (hφΩ hxφ))
      rw [hz, zero_mul]
    change (∫ x, φ x * ((g x) i - (h x) i)) = 0
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    simp_rw [mul_sub, mul_comm (φ _)]
    rw [integral_sub hgp hhp, heq, sub_self]
  apply (ae_restrict_iff' hΩ.measurableSet).2
  filter_upwards [ae_all_iff.2 hcoord] with x hx hxΩ
  ext i
  exact sub_eq_zero.mp (hx i hxΩ)

theorem SobolevPair.gradient_ae_unique {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g h : Space n → Space n}
    (hg : SobolevPair p Ω u g) (hh : SobolevPair p Ω u h)
    (hΩ : IsOpen Ω) : g =ᵐ[volume.restrict Ω] h := by
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hg.1.le)
  exact hg.2.2.2.ae_unique hh.2.2.2 hΩ
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hg.2.2.1.locallyIntegrable hp))
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hh.2.2.1.locallyIntegrable hp))

end BMCompactPDE

#print axioms BMCompactPDE.HasWeakGradientOn.ae_unique
#print axioms BMCompactPDE.SobolevPair.gradient_ae_unique
