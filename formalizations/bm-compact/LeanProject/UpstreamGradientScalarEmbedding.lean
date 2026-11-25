import PotentialSobolevBoost
import RootW0Linear

/-! Actual finite local scalar integrability in the critical/supercritical
Sobolev range. A bounded collar lowers the exponent to r=2*n/3; a genuinely
constructed compact cutoff and actual W0_r embedding yield L^(2*n). No scalar
continuity, bound, PDE, or higher integrability is an input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 800000 in
/-- Any actual W1,p pair with p>=n,n>=2 has scalar L^(2*n) membership on each
relatively compact open subdomain. No boundedness of the ambient domain is
needed, and the original weak-gradient identity is retained in the proof. -/
theorem SobolevPair.memLp_local_twice_dimension
    {n : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hΩ : IsOpen Ω) (hn : 2≤n) (hnp : (n:ℝ)≤p)
    (hD : LocalDomain D Ω) :
    MemLp u (ENNReal.ofReal (2*(n:ℝ))) (volume.restrict D) := by
  have hnR : (2:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have hn0 : 0<(n:ℝ) := by linarith
  let r : ℝ := 2*(n:ℝ)/3
  have hr : 1<r := by dsimp only [r];linarith
  have hrn : r<(n:ℝ) := by dsimp only [r];linarith
  have hrp : r≤p := le_trans hrn.le hnp
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_cthickening_subset_open hΩ hD.2.2
  let U : Set (Space n) := thickening δ (closure D)
  have hU : LocalDomain U Ω := by
    refine ⟨isOpen_thickening,hK.isBounded.thickening,?_⟩
    exact (closure_thickening_subset_cthickening δ (closure D)).trans hthick
  have hDU : LocalDomain D U :=
    ⟨hD.1,hD.2.1,self_subset_thickening hδ (closure D)⟩
  have huU := hu.mono_actual (subset_closure.trans hU.2.2)
  letI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hU.2.1.measure_lt_top.ne
  have hSr : SobolevPair r U u g :=
    ⟨hr,huU.2.1.mono_exponent (ENNReal.ofReal_le_ofReal hrp),
      huU.2.2.1.mono_exponent (ENNReal.ofReal_le_ofReal hrp),huU.2.2.2⟩
  obtain ⟨a,ha⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hU.1 hDU.2.2
  let χ : Space n → ℝ := fun x => Real.smoothTransition (a x)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp ha.1
  have hχc : HasCompactSupport χ := ha.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0:ℝ)))
  have hχs : tsupport χ⊆U :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0:ℝ))) a).trans ha.2.2.1
  have hχ1 (x : Space n) (hx : x∈D) : χ x=1 :=
    Real.smoothTransition.one_of_one_le (ha.2.2.2 x (subset_closure hx))
  have hz := hSr.mul_smooth_compactSupport_zeroBoundary hU.1 hχ hχc hχs
  have hboost := (hz.critical_sobolev_explicit hrn).1
  have he : (n:ℝ)*r/((n:ℝ)-r)=2*(n:ℝ) := by
    dsimp only [r]
    field_simp
    <;> ring
  rw [he] at hboost
  have hd := hboost.mono_measure (Measure.restrict_mono_set volume
    (subset_closure.trans hDU.2.2))
  apply hd.ae_eq
  filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
  simp only [hχ1 x hx,one_mul]

end BMCompactPDE
#print axioms BMCompactPDE.SobolevPair.memLp_local_twice_dimension
