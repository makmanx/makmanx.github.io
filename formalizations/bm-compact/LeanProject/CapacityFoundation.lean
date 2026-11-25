import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Support

/-!
Concrete variational definitions for BM_Compact_Final.tex, source labels
eqn1.4 and eqn2.15. Energies are nonnegative extended
reals, so an empty admissible class has infimum infinity rather than zero.
The energy uses the actual Euclidean gradient.
This file does not postulate any capacitary Brunn--Minkowski inequality.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal ContDiff

namespace BMCompactCapacityV2

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def Admissible {n : ℕ} (K O : Set (Space n)) (f : Space n → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ O ∧
    ∀ x ∈ K, (1 : ℝ) ≤ f x

def pEnergy {n : ℕ} (p : ℝ) (O : Set (Space n)) (f : Space n → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in O, ENNReal.ofReal (‖gradient f x‖ ^ p)

def relativeCapacity {n : ℕ} (p : ℝ) (K O : Set (Space n)) : ℝ≥0∞ :=
  ⨅ (f : Space n → ℝ) (_ : Admissible K O f), pEnergy p O f

def variationalCapacity {n : ℕ} (p : ℝ) (K : Set (Space n)) : ℝ≥0∞ :=
  relativeCapacity p K univ

theorem admissible_of_subset {n : ℕ} {K L O : Set (Space n)}
    {f : Space n → ℝ} (hKL : K ⊆ L) (hf : Admissible L O f) :
    Admissible K O f :=
  ⟨hf.1, hf.2.1, hf.2.2.1, fun x hx => hf.2.2.2 x (hKL hx)⟩

/-- Actual set monotonicity of the concrete relative variational capacity. -/
theorem relativeCapacity_mono {n : ℕ} (p : ℝ) {K L O : Set (Space n)}
    (hKL : K ⊆ L) : relativeCapacity p K O ≤ relativeCapacity p L O := by
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  exact iInf_le_of_le f (iInf_le_of_le (admissible_of_subset hKL hf) le_rfl)

theorem variationalCapacity_mono {n : ℕ} (p : ℝ) {K L : Set (Space n)}
    (hKL : K ⊆ L) : variationalCapacity p K ≤ variationalCapacity p L :=
  relativeCapacity_mono p hKL

/-- Each individual admissible function bounds the infimum from above. -/
theorem relativeCapacity_le_energy {n : ℕ} (p : ℝ) {K O : Set (Space n)}
    {f : Space n → ℝ} (hf : Admissible K O f) :
    relativeCapacity p K O ≤ pEnergy p O f :=
  iInf_le_of_le f (iInf_le_of_le hf le_rfl)

end BMCompactCapacityV2

#print axioms BMCompactCapacityV2.admissible_of_subset
#print axioms BMCompactCapacityV2.relativeCapacity_mono
#print axioms BMCompactCapacityV2.variationalCapacity_mono
#print axioms BMCompactCapacityV2.relativeCapacity_le_energy

namespace BMCompactCapacityV2

theorem gradient_hasCompactSupport {n : ℕ} {f : Space n → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (gradient f) := by
  change HasCompactSupport (fun x => (InnerProductSpace.toDual ℝ (Space n)).symm (fderiv ℝ f x))
  exact (hf.fderiv ℝ).comp_left
      (g := (InnerProductSpace.toDual ℝ (Space n)).symm) (map_zero _)

theorem continuous_gradient_of_contDiff {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) : Continuous (gradient f) := by
  exact (InnerProductSpace.toDual ℝ (Space n)).symm.continuous.comp
    (hf.continuous_fderiv (by simp))

theorem smooth_compactSupport_memLp {n : ℕ} (q : ℝ≥0∞)
    {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    MemLp f q volume := hf.continuous.memLp_of_hasCompactSupport hfc

theorem gradient_smooth_compactSupport_memLp {n : ℕ} (q : ℝ≥0∞)
    {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    MemLp (gradient f) q volume :=
  (continuous_gradient_of_contDiff hf).memLp_of_hasCompactSupport
    (gradient_hasCompactSupport hfc)

theorem gradient_const_mul {n : ℕ} (c : ℝ) (f : Space n → ℝ) (x : Space n) :
    gradient (fun y => c * f y) x = c • gradient f x := by
  unfold gradient
  have hderiv : fderiv ℝ (fun y => c * f y) x = c • fderiv ℝ f x := by
    change fderiv ℝ (c • f) x = c • fderiv ℝ f x
    exact congrFun (fderiv_const_smul_field (f := f) c) x
  rw [hderiv]
  exact map_smul (InnerProductSpace.toDual ℝ (Space n)).symm c (fderiv ℝ f x)

theorem pEnergy_const_mul {n : ℕ} (p c : ℝ) (O : Set (Space n))
    (f : Space n → ℝ) :
    pEnergy p O (fun y => c * f y) = ENNReal.ofReal (|c| ^ p) * pEnergy p O f := by
  unfold pEnergy
  simp_rw [gradient_const_mul, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg c) p)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem pEnergy_ne_top_of_smooth_compactSupport {n : ℕ} (p : ℝ) (hp : 0 < p)
    (O : Set (Space n)) {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    pEnergy p O f ≠ (∞ : ℝ≥0∞) := by
  have hcont : Continuous (fun x => ‖gradient f x‖ ^ p) :=
    (continuous_gradient_of_contDiff hf).norm.rpow_const (fun _ => Or.inr hp.le)
  have hcomp : HasCompactSupport (fun x => ‖gradient f x‖ ^ p) :=
    ((gradient_hasCompactSupport hfc).comp_left (g := fun v => ‖v‖) (norm_zero)).rpow_const hp.ne'
  have hint : Integrable (fun x => ‖gradient f x‖ ^ p) :=
    hcont.integrable_of_hasCompactSupport hcomp
  have hintO := hint.integrableOn (s := O)
  exact (lintegral_ofReal_ne_top_iff_integrable hintO.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) p))).2 hintO

theorem gradient_eq_zero_of_notMem_tsupport {n : ℕ} {f : Space n → ℝ}
    {x : Space n} (hx : x ∉ tsupport f) : gradient f x = 0 := by
  simp [gradient, fderiv_of_notMem_tsupport ℝ hx]

theorem pEnergy_eq_univ_of_tsupport_subset {n : ℕ} (p : ℝ) (hp : p ≠ 0)
    {O : Set (Space n)} {f : Space n → ℝ} (hfO : tsupport f ⊆ O) :
    pEnergy p O f = pEnergy p univ f := by
  have hsupp : Function.support (fun x => ENNReal.ofReal (‖gradient f x‖ ^ p)) ⊆ O := by
    intro x hx
    by_contra hxO
    have hxf : x ∉ tsupport f := fun h => hxO (hfO h)
    have hzero : ENNReal.ofReal (‖gradient f x‖ ^ p) = 0 := by
      simp [gradient_eq_zero_of_notMem_tsupport hxf, Real.zero_rpow hp]
    exact hx hzero
  simpa [pEnergy] using (setLIntegral_eq_of_support_subset (μ := volume) hsupp)

theorem relativeCapacity_mono_domain {n : ℕ} (p : ℝ) (hp : p ≠ 0)
    {K O P : Set (Space n)} (hOP : O ⊆ P) :
    relativeCapacity p K P ≤ relativeCapacity p K O := by
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  have hfP : Admissible K P f := ⟨hf.1, hf.2.1, hf.2.2.1.trans hOP, hf.2.2.2⟩
  calc
    relativeCapacity p K P ≤ pEnergy p P f := relativeCapacity_le_energy p hfP
    _ = pEnergy p univ f := pEnergy_eq_univ_of_tsupport_subset p hp hfP.2.2.1
    _ = pEnergy p O f := (pEnergy_eq_univ_of_tsupport_subset p hp hf.2.2.1).symm

theorem relativeCapacity_empty {n : ℕ} (p : ℝ) (hp : p ≠ 0)
    (O : Set (Space n)) : relativeCapacity p ∅ O = 0 := by
  have hz : Admissible (∅ : Set (Space n)) O (fun _ => (0 : ℝ)) := by
    refine ⟨contDiff_const, ?_, ?_, ?_⟩
    · exact HasCompactSupport.zero
    · simp
    · simp
  apply le_antisymm _ bot_le
  calc
    relativeCapacity p ∅ O ≤ pEnergy p O (fun _ => 0) := relativeCapacity_le_energy p hz
    _ = 0 := by simp [pEnergy, gradient_fun_const, Real.zero_rpow hp]

theorem variationalCapacity_empty {n : ℕ} (p : ℝ) (hp : p ≠ 0) :
    variationalCapacity p (∅ : Set (Space n)) = 0 :=
  relativeCapacity_empty p hp univ

theorem tsupport_finset_sum_subset {n : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → Space n → ℝ) (O : Set (Space n))
    (hg : ∀ i ∈ s, tsupport (g i) ⊆ O) :
    tsupport (∑ i ∈ s, g i) ⊆ O := by
  classical
  revert hg
  induction s using Finset.induction_on with
  | empty => intro hg; simp
  | @insert a s ha ih =>
    intro hg
    rw [Finset.sum_insert ha]
    exact (tsupport_add _ _).trans (union_subset (hg a (by simp))
      (ih (fun i hi => hg i (by simp [hi]))))

/-- A genuine smooth admissible cutoff for every compact set inside an open set. -/
theorem exists_admissible_of_isCompact {n : ℕ} {K O : Set (Space n)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ f : Space n → ℝ, Admissible K O f := by
  classical
  have hlocal : ∀ a : K, ∃ b : ContDiffBump (a : Space n), tsupport b ⊆ O := by
    intro a
    obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.1 (hO.mem_nhds (hKO a.property))
    let b : ContDiffBump (a : Space n) :=
      { rIn := r / 4, rOut := r / 2, rIn_pos := by positivity,
        rIn_lt_rOut := by linarith }
    refine ⟨b, ?_⟩
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (half_lt_self hr)).trans hrO
  choose b hb using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun a : K => Metric.ball (a : Space n) (b a).rIn)
    (fun _ => Metric.isOpen_ball) (fun x hx =>
      mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (b ⟨x, hx⟩).rIn_pos⟩)
  let f : Space n → ℝ := ∑ a ∈ s, (b a : Space n → ℝ)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · have hsum : f = (fun x : Space n => ∑ a ∈ s, (b a) x) := by
      funext x
      simp only [f, Finset.sum_apply]
    rw [hsum]
    exact ContDiff.sum (fun a ha => (b a).contDiff)
  · exact HasCompactSupport.finset_sum (fun a ha => (b a).hasCompactSupport)
  · exact tsupport_finset_sum_subset s (fun a => (b a : Space n → ℝ)) O (fun a ha => hb a)
  · intro x hx
    obtain ⟨a, ha, hax⟩ := mem_iUnion₂.1 (hs hx)
    have hba : (b a) x = 1 := (b a).one_of_mem_closedBall (Metric.ball_subset_closedBall hax)
    change 1 ≤ (∑ a ∈ s, (b a : Space n → ℝ)) x
    simp only [Finset.sum_apply]
    calc
      1 = (b a) x := hba.symm
      _ ≤ ∑ i ∈ s, (b i) x := Finset.single_le_sum (fun i hi => (b i).nonneg) ha

/-- Scaling any smooth competitor up slightly makes it admissible on an open
neighborhood of the original set, with the exact energy cost. -/
theorem exists_open_admissible_const_mul {n : ℕ} {K O : Set (Space n)}
    {f : Space n → ℝ} (hf : Admissible K O f) {c : ℝ} (hc : 1 < c) :
    ∃ U : Set (Space n), IsOpen U ∧ K ⊆ U ∧ U ⊆ O ∧
      Admissible U O (fun x => c * f x) := by
  let U : Set (Space n) := {x | 1 < c * f x}
  have hc0 : 0 ≤ c := (zero_lt_one.trans hc).le
  refine ⟨U, isOpen_lt continuous_const (continuous_const.mul hf.1.continuous), ?_, ?_, ?_⟩
  · intro x hx
    change 1 < c * f x
    exact hc.trans_le (by simpa using mul_le_mul_of_nonneg_left (hf.2.2.2 x hx) hc0)
  · intro x hx
    apply hf.2.2.1
    apply subset_tsupport f
    intro hz
    have hh : 1 < c * f x := hx
    rw [hz, mul_zero] at hh
    exact (not_lt_of_ge zero_le_one) hh
  · refine ⟨contDiff_const.mul hf.1, ?_, ?_, ?_⟩
    · exact hf.2.1.comp_left (g := fun y : ℝ => c * y) (mul_zero c)
    · exact tsupport_mul_subset_right.trans hf.2.2.1
    · intro x hx
      exact le_of_lt hx

theorem exists_open_capacity_le_scaled_energy {n : ℕ} (p : ℝ)
    {K O : Set (Space n)} {f : Space n → ℝ} (hf : Admissible K O f)
    {c : ℝ} (hc : 1 < c) :
    ∃ U : Set (Space n), IsOpen U ∧ K ⊆ U ∧ U ⊆ O ∧
      relativeCapacity p U O ≤ ENNReal.ofReal (|c| ^ p) * pEnergy p O f := by
  obtain ⟨U, hU, hKU, hUO, hUf⟩ := exists_open_admissible_const_mul hf hc
  refine ⟨U, hU, hKU, hUO, ?_⟩
  exact (relativeCapacity_le_energy p hUf).trans_eq (pEnergy_const_mul p c O f)

theorem relativeCapacity_ne_top_of_isCompact {n : ℕ} (p : ℝ) (hp : 0 < p)
    {K O : Set (Space n)} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    relativeCapacity p K O ≠ (∞ : ℝ≥0∞) := by
  obtain ⟨f, hf⟩ := exists_admissible_of_isCompact hK hO hKO
  exact ne_of_lt (lt_of_le_of_lt (relativeCapacity_le_energy p hf)
    (lt_top_iff_ne_top.2 (pEnergy_ne_top_of_smooth_compactSupport p hp O hf.1 hf.2.1)))

theorem variationalCapacity_ne_top_of_isCompact {n : ℕ} (p : ℝ) (hp : 0 < p)
    {K : Set (Space n)} (hK : IsCompact K) : variationalCapacity p K ≠ (∞ : ℝ≥0∞) :=
  relativeCapacity_ne_top_of_isCompact p hp hK isOpen_univ (subset_univ _)

end BMCompactCapacityV2

#print axioms BMCompactCapacityV2.gradient_hasCompactSupport
#print axioms BMCompactCapacityV2.continuous_gradient_of_contDiff
#print axioms BMCompactCapacityV2.pEnergy_ne_top_of_smooth_compactSupport
#print axioms BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
#print axioms BMCompactCapacityV2.pEnergy_eq_univ_of_tsupport_subset
#print axioms BMCompactCapacityV2.relativeCapacity_mono_domain
#print axioms BMCompactCapacityV2.relativeCapacity_empty
#print axioms BMCompactCapacityV2.variationalCapacity_empty
#print axioms BMCompactCapacityV2.tsupport_finset_sum_subset
#print axioms BMCompactCapacityV2.exists_admissible_of_isCompact
#print axioms BMCompactCapacityV2.relativeCapacity_ne_top_of_isCompact
#print axioms BMCompactCapacityV2.variationalCapacity_ne_top_of_isCompact

#print axioms BMCompactCapacityV2.smooth_compactSupport_memLp
#print axioms BMCompactCapacityV2.gradient_smooth_compactSupport_memLp
#print axioms BMCompactCapacityV2.gradient_const_mul
#print axioms BMCompactCapacityV2.pEnergy_const_mul

#print axioms BMCompactCapacityV2.exists_open_admissible_const_mul
#print axioms BMCompactCapacityV2.exists_open_capacity_le_scaled_energy
