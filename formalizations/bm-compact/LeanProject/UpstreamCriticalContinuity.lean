import UpstreamMorreyLocal
import UpstreamGradientHigherIntegrability
import UpstreamGradientScalarEmbedding
import UpstreamGradientTwoDimensionalGain

/-! Actual selected continuity in the critical range. Scalar and gradient
integrability gains are derived from the raw weak PDE, and a larger actual
Sobolev exponent supplies Morrey continuity. The original p-source operator
and independently supplied gradient are retained, not recast at that exponent.
No continuity, oscillation, bound or higher-integrability premise is supplied. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem upstream_source_scalar_twice_dimension
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hn : 2≤n) (hnp : (n:ℝ)≤p)
    (hD : LocalDomain D Ω) :
    MemLp u (ENNReal.ofReal (2*(n:ℝ))) (volume.restrict D) := by
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_cthickening_subset_open hu.2.1 hD.2.2
  let U : Set (Space n) := thickening δ (closure D)
  have hU : LocalDomain U Ω := by
    refine ⟨isOpen_thickening,hK.isBounded.thickening,?_⟩
    exact (closure_thickening_subset_cthickening δ (closure D)).trans hthick
  have hDU : LocalDomain D U :=
    ⟨hD.1,hD.2.1,self_subset_thickening hδ (closure D)⟩
  exact (hu.2.2.1 U hU).memLp_local_twice_dimension hU.1 hn hnp hDU

private theorem upstream_source_representative_from_larger_sobolev
    {n : ℕ} {p q c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hn : 1≤n) (hnq : (n:ℝ)<q)
    (hdata : ∀ D,LocalDomain D Ω → SobolevPair q D u g) :
    ∃ v : Space n → ℝ,ContinuousOn v Ω ∧ u =ᵐ[volume.restrict Ω] v ∧
      WeakPSourcePair p c Ω v g := by
  obtain ⟨v,hv,huv,-⟩ :=
    exists_unique_continuousRepresentative_of_local_supercritical_sobolev
      hu.2.1 hn hnq hdata
  exact ⟨v,hv,huv,hu.1,hu.2.1,hu.2.2.1.congr_ae huv EventuallyEq.rfl,hu.2.2.2⟩

/-- Every actual constant-source weak solution in the critical range p=n>=2
has a continuous representative satisfying the SAME original weak equation
with the SAME supplied gradient. Actual local Sobolev gains supply Morrey. -/
theorem WeakPSourcePair.exists_continuous_weak_representative_critical
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hn : 2≤n) (hpn : p=(n:ℝ)) :
    ∃ v : Space n → ℝ,ContinuousOn v Ω ∧ u =ᵐ[volume.restrict Ω] v ∧
      WeakPSourcePair p c Ω v g := by
  subst p
  have hn1 : 1≤n := (by decide : 1≤2).trans hn
  by_cases htwo : n=2
  · subst n
    apply upstream_source_representative_from_larger_sobolev (q:=4) hu
      (by decide : 1≤2) (by norm_num : (2:ℝ)<4)
    intro D hD
    have hfu := upstream_source_scalar_twice_dimension hu (by decide) (le_refl _) hD
    have hfg := hu.memLp_gradient_first_sobolev_gain_two (by norm_num) hD
    norm_num at hfu hfg
    exact ⟨by norm_num,by simpa only [ENNReal.ofReal_ofNat] using hfu,
      by simpa only [ENNReal.ofReal_ofNat] using hfg,(hu.2.2.1 D hD).2.2.2⟩
  · have hn3 : 3≤n := by omega
    have hnR : (2:ℝ)<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 2<3) hn3)
    have hn0 : 0<(n:ℝ) := by linarith only [hnR]
    let s : ℝ := (n:ℝ)*(n:ℝ)/((n:ℝ)-2)
    let q : ℝ := min (2*(n:ℝ)) s
    have hsn : (n:ℝ)<s := by
      apply (lt_div_iff₀ (by linarith only [hnR] : 0<(n:ℝ)-2)).mpr
      nlinarith only [hn0]
    have hqn : (n:ℝ)<q := lt_min (by linarith only [hn0]) hsn
    have hq1 : 1<q := (by linarith only [hnR] : (1:ℝ)<(n:ℝ)).trans hqn
    apply upstream_source_representative_from_larger_sobolev (q:=q) hu hn1 hqn
    intro D hD
    letI : IsFiniteMeasure (volume.restrict D) :=
      isFiniteMeasure_restrict.mpr hD.2.1.measure_lt_top.ne
    have hfu := upstream_source_scalar_twice_dimension hu hn (le_refl _) hD
    have hfg := hu.memLp_gradient_first_sobolev_gain hnR.le hn3 hD
    refine ⟨hq1,?_,?_,(hu.2.2.1 D hD).2.2.2⟩
    · exact hfu.mono_exponent (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    · exact hfg.mono_exponent (ENNReal.ofReal_le_ofReal (min_le_right _ _))

/-- All exponents p>1 are now covered for actual constant-source weak pairs
in n>=2. Below dimension use the retained actual De Giorgi theorem; at the
critical exponent use derived Sobolev gains; above dimension use Morrey. -/
theorem WeakPSourcePair.exists_continuous_weak_representative_allp
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hn : 2≤n) :
    ∃ v : Space n → ℝ,ContinuousOn v Ω ∧ u =ᵐ[volume.restrict Ω] v ∧
      WeakPSourcePair p c Ω v g := by
  rcases lt_trichotomy p (n:ℝ) with hsub|hcrit|hsuper
  · exact hu.exists_continuous_weak_representative hsub
  · exact hu.exists_continuous_weak_representative_critical hn hcrit
  · exact hu.exists_continuous_weak_representative_supercritical
      ((by decide : 1≤2).trans hn) hsuper

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.exists_continuous_weak_representative_critical
#print axioms BMCompactPDE.WeakPSourcePair.exists_continuous_weak_representative_allp
