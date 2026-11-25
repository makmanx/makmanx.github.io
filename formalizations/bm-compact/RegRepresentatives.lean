import BMCompactChecked
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! Regularity must select the correct a.e. representative. The weak model is
properly a.e.-invariant; a raw pointwise representative can have a removable
spike and fail continuity even while being genuinely weak p-harmonic. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
namespace BMCompactPDE

theorem LocallySobolevPair.congr_ae {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : LocallySobolevPair p Ω u g)
    (huv : u =ᵐ[volume.restrict Ω] v) (hgh : g =ᵐ[volume.restrict Ω] h) :
    LocallySobolevPair p Ω v h := by
  intro D hD
  have hDO : D ⊆ Ω := subset_closure.trans hD.2.2
  exact (hu D hD).congr
    (ae_restrict_of_ae_restrict_of_subset hDO huv)
    (ae_restrict_of_ae_restrict_of_subset hDO hgh)

theorem WeakPHarmonicPair.congr_ae {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g)
    (huv : u =ᵐ[volume.restrict Ω] v) (hgh : g =ᵐ[volume.restrict Ω] h) :
    WeakPHarmonicPair p Ω v h := by
  refine ⟨hu.1,hu.2.1,hu.2.2.1.congr_ae huv hgh,?_⟩
  intro D hD θ k hθ
  obtain ⟨hi,hzero⟩ := hu.2.2.2 D hD θ k hθ
  have hae := ae_restrict_of_ae_restrict_of_subset
    (subset_closure.trans hD.2.2) hgh
  have he : fluxPairing p g k =ᵐ[volume.restrict D] fluxPairing p h k := by
    filter_upwards [hae] with x hx
    simp only [fluxPairing,hx]
  exact ⟨hi.congr he,by rw [←integral_congr_ae he]; exact hzero⟩

theorem IsWeakPHarmonic.congr_ae {n : ℕ} {p : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} (hu : IsWeakPHarmonic p Ω u)
    (huv : u =ᵐ[volume.restrict Ω] v) : IsWeakPHarmonic p Ω v := by
  obtain ⟨g,hg⟩ := hu
  exact ⟨g,hg.congr_ae huv EventuallyEq.rfl⟩

def regPointSpike (x : Space 2) : ℝ := if x=0 then 1 else 0

theorem regPointSpike_ae_zero : regPointSpike =ᵐ[volume] (0 : Space 2 → ℝ) := by
  have hne : ∀ᵐ x : Space 2 ∂volume, x ≠ 0 := by
    exact Measure.ae_ne volume 0
  filter_upwards [hne] with x hx
  simp only [regPointSpike,if_neg hx,Pi.zero_apply]

theorem weakPHarmonicPair_regPointSpike {p : ℝ} (hp : 1 < p) :
    WeakPHarmonicPair p univ regPointSpike (0 : Space 2 → Space 2) := by
  apply (weakPHarmonicPair_zero hp isOpen_univ).congr_ae
  · simpa only [Measure.restrict_univ] using regPointSpike_ae_zero.symm
  · exact EventuallyEq.rfl

theorem not_continuous_regPointSpike : ¬Continuous regPointSpike := by
  intro hc
  have hae : regPointSpike =ᵐ[volume.restrict univ] (0 : Space 2 → ℝ) := by
    simpa only [Measure.restrict_univ] using regPointSpike_ae_zero
  have he := Measure.eqOn_open_of_ae_eq hae isOpen_univ hc.continuousOn continuousOn_const
  have hz := he (mem_univ (0 : Space 2))
  norm_num [regPointSpike] at hz

/-- General weak regularity cannot mean continuity of every raw representative.
It must supply a suitable a.e.-equal representative, as the manuscript does. -/
theorem exists_weakPHarmonic_not_continuous {p : ℝ} (hp : 1 < p) :
    ∃ u : Space 2 → ℝ, IsWeakPHarmonic p univ u ∧ ¬Continuous u ∧
      u =ᵐ[volume] (0 : Space 2 → ℝ) :=
  ⟨regPointSpike,⟨0,weakPHarmonicPair_regPointSpike hp⟩,
    not_continuous_regPointSpike,regPointSpike_ae_zero⟩

end BMCompactPDE
#print axioms BMCompactPDE.LocallySobolevPair.congr_ae
#print axioms BMCompactPDE.WeakPHarmonicPair.congr_ae
#print axioms BMCompactPDE.IsWeakPHarmonic.congr_ae
#print axioms BMCompactPDE.regPointSpike_ae_zero
#print axioms BMCompactPDE.weakPHarmonicPair_regPointSpike
#print axioms BMCompactPDE.not_continuous_regPointSpike
#print axioms BMCompactPDE.exists_weakPHarmonic_not_continuous
