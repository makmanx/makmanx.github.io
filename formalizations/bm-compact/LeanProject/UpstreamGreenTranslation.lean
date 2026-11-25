import UpstreamGreenExistenceSupercritical
import GradientAnalyticBatch
import RadialTranslationLimit
import Mathlib.Topology.Bornology.BoundedOperation

/-! Actual translation of weak exterior Green functions. The remainder stays
normalized against the ORIGINAL canonical radial profile: its translation
difference genuinely tends to zero. Supercritical existence consequently
holds for every nonempty compact obstacle, without a coordinate assumption.
No finite asymptotic constant or nonlinear C1 conclusion is asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric Bornology
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem green_translated_complement {n : ℕ} (K : Set (Space n)) (a : Space n) :
    (fun x : Space n=>x+(-a)) ⁻¹' Kᶜ=((fun x : Space n=>x+a) '' K)ᶜ := by
  ext x
  change (x+(-a)∉K) ↔ x∉(fun y : Space n=>y+a) '' K
  constructor
  · intro h hx
    obtain ⟨y,hy,he⟩ := hx
    apply h
    have he' : x+(-a)=y := by rw [←he,add_neg_cancel_right]
    exact he' ▸ hy
  · intro h hx
    apply h
    exact ⟨x+(-a),hx,neg_add_cancel_right x a⟩

/-- Translation preserves the actual weak exterior Green predicate, including
its normalization by the unshifted radial profile and actual full weak PDE. -/
theorem IsExteriorGreen.translate_actual
    {n : ℕ} {σ p : ℝ} {K : Set (Space n)} {G : Space n → ℝ}
    (hG : IsExteriorGreen n σ p K G) (a : Space n) :
    IsExteriorGreen n σ p ((fun x : Space n=>x+a) '' K) (fun x=>G (x-a)) := by
  obtain ⟨hn,hpn,hσ,hK,hKne,hGc,hGK,⟨g,hGPDE⟩,C,hC,hRem⟩ := hG
  have hPDE : WeakPHarmonicPair p (((fun x : Space n=>x+a) '' K)ᶜ)
      (fun x=>G (x-a)) (fun x=>g (x-a)) := by
    have ht := hGPDE.source_zero.translate_actual (-a)
    rw [green_translated_complement K a] at ht
    simpa only [sub_eq_add_neg] using ht.harmonic_of_source_zero
  have htail : ∀ᶠ x : Space n in cobounded (Space n),
      |G (x-a)-fundamentalPotential n σ p (x-a)|≤C :=
    (tendsto_sub_const_cobounded a).eventually hRem
  have hdiff : ∀ᶠ x : Space n in cobounded (Space n),
      |fundamentalPotential n σ p (x-a)-fundamentalPotential n σ p x|<1 := by
    have ht := (tendsto_fundamentalPotential_translate_sub n σ hn hpn a).abs
    exact ht.eventually (eventually_lt_nhds (by norm_num : |(0:ℝ)|<1))
  refine ⟨hn,hpn,hσ,hK.image (continuous_id.add continuous_const),
    hKne.image _,hGc.comp (continuous_id.sub continuous_const),?_,⟨_,hPDE⟩,C+1,by linarith only [hC],?_⟩
  · rintro x ⟨y,hy,rfl⟩
    simpa only [add_sub_cancel_right] using hGK hy
  · filter_upwards [htail,hdiff] with x hx hy
    calc
      |G (x-a)-fundamentalPotential n σ p x|=
          |(G (x-a)-fundamentalPotential n σ p (x-a))+
            (fundamentalPotential n σ p (x-a)-fundamentalPotential n σ p x)| := by congr 1;ring
      _≤|G (x-a)-fundamentalPotential n σ p (x-a)|+
          |fundamentalPotential n σ p (x-a)-fundamentalPotential n σ p x| := abs_add_le _ _
      _≤C+1 := add_le_add hx hy.le

/-- Genuine canonical weak exterior Green existence for EVERY nonempty compact
obstacle above the dimension. Choosing a point and translating the actual
annular construction discharges the coordinate normalization; the original
unshifted canonical profile still defines the bounded remainder. -/
theorem exists_canonical_exterior_green_supercritical_nonempty
    {n : ℕ} {p : ℝ} (hn : 2≤n) (hnp : (n:ℝ)<p)
    {K : Set (Space n)} (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ G : Space n → ℝ,∃ g : Space n → Space n,
      IsExteriorGreen n (canonicalSphereArea n) p K G ∧ WeakPHarmonicPair p Kᶜ G g := by
  obtain ⟨a,ha⟩ := hKne
  let K₀ : Set (Space n) := (fun x : Space n=>x-a) '' K
  have hK₀ : IsCompact K₀ := hK.image (continuous_id.sub continuous_const)
  have hzero : (0 : Space n)∈K₀ := ⟨a,ha,sub_self a⟩
  obtain ⟨G,_,hG,-,-,-⟩ := exists_canonical_exterior_green_supercritical hn hnp hK₀ hzero
  have hback : (fun x : Space n=>x+a) '' K₀=K := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      simpa only [sub_add_cancel] using hz
    · intro hx
      exact ⟨x-a,⟨x,hx,rfl⟩,sub_add_cancel x a⟩
  have ht := hG.translate_actual a
  rw [hback] at ht
  obtain ⟨g,hg⟩ := ht.2.2.2.2.2.2.2.1
  exact ⟨_,g,ht,hg⟩

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.translate_actual
#print axioms BMCompactPDE.exists_canonical_exterior_green_supercritical_nonempty
