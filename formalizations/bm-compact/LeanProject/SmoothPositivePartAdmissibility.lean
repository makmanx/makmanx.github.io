import SmoothPositivePart
import LpDominatedLimit
import WeakPositivePartComparison
import RadialSobolev
import Mathlib.MeasureTheory.Integral.DominatedConvergence


/-! The positive part of a genuine C∞ function has the concrete weak gradient
obtained by cutting its classical gradient at the positive set. This is proved
by flat smooth approximation and integration by parts, including at zero. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace BMCompactPDE

def positivePartGradient {n : ℕ} (u : Space n → ℝ) (g : Space n → Space n) :
    Space n → Space n := fun x => if 0 < u x then g x else 0

theorem positivePartGradient_aestronglyMeasurable {n : ℕ} {u : Space n → ℝ}
    {g : Space n → Space n} (hu : Continuous u) (hg : Continuous g)
    (μ : Measure (Space n)) : AEStronglyMeasurable (positivePartGradient u g) μ := by
  have hm : MeasurableSet {x : Space n | 0 < u x} :=
    isOpen_lt continuous_const hu |>.measurableSet
  change AEStronglyMeasurable ({x : Space n | 0 < u x}.indicator g) μ
  exact hg.aestronglyMeasurable.indicator hm

theorem positivePartGradient_norm_le {n : ℕ} (u : Space n → ℝ)
    (g : Space n → Space n) (x : Space n) :
    ‖positivePartGradient u g x‖ ≤ ‖g x‖ := by
  simp only [positivePartGradient]
  split_ifs <;> simp

theorem hasWeakGradientOn_positivePart_of_contDiff {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (Ω : Set (Space n)) :
    HasWeakGradientOn Ω (fun x => max (u x) 0) (positivePartGradient u (gradient u)) := by
  intro φ hφ i
  let μ := volume.restrict Ω
  let g := gradient u
  let G := positivePartGradient u g
  have hg : Continuous g := BMCompactCapacityV2.continuous_gradient_of_contDiff hu
  have hG : AEStronglyMeasurable G μ :=
    positivePartGradient_aestronglyMeasurable hu.continuous hg μ
  have hGi : AEStronglyMeasurable (fun x => (G x) i) μ :=
    (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hG
  have hφmeas := hφ.1.continuous.aestronglyMeasurable (μ := μ)
  have hgradφ : Continuous (gradient φ) :=
    BMCompactCapacityV2.continuous_gradient_of_contDiff hφ.1
  have hφdmeas : AEStronglyMeasurable (fun x => (gradient φ x) i) μ :=
    (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hgradφ.aestronglyMeasurable
  have hbase := hasWeakGradientOn_of_contDiff hu Ω φ hφ i
  have hmax : AEStronglyMeasurable (fun x => max (u x) 0) μ :=
    (hu.continuous.max continuous_const).aestronglyMeasurable
  have hnormmax (x : Space n) : ‖max (u x) 0‖ ≤ ‖u x‖ := by
    by_cases hx : u x ≤ 0
    · simp [max_eq_right hx]
    · rw [max_eq_left (lt_of_not_ge hx).le]
  have hleft : Integrable (fun x => max (u x) 0 * (gradient φ x) i) μ :=
    hbase.1.mono (hmax.mul hφdmeas) (Eventually.of_forall (fun x => by
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_right (hnormmax x) (norm_nonneg _)))
  have hright : Integrable (fun x => (G x) i * φ x) μ := by
    apply hbase.2.1.mono (hGi.mul hφmeas)
    exact Eventually.of_forall (fun x => by
      dsimp [G, positivePartGradient, g]
      split_ifs <;> simp <;> positivity)
  obtain ⟨C, hC, hboundC⟩ := positivePartSlope_uniform_bound
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have htest (j : ℕ) := hasWeakGradientOn_of_contDiff
    ((smoothPositivePart_contDiff j).comp hu) Ω φ hφ i
  have hleftlim : Tendsto
      (fun j => ∫ x, smoothPositivePart j (u x) * (gradient φ x) i ∂μ)
      atTop (𝓝 (∫ x, max (u x) 0 * (gradient φ x) i ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖u x * (gradient φ x) i‖)
    · intro j
      exact (htest j).1.1
    · exact hbase.1.norm
    · intro j
      exact Eventually.of_forall (fun x => by
        simp only [norm_mul]
        exact mul_le_mul_of_nonneg_right (smoothPositivePart_norm_le j (u x)) (norm_nonneg _))
    · exact Eventually.of_forall (fun x =>
        tendsto_const_nhds.congr' ((smoothPositivePart_eventually_eq (u x)).mono
          (fun j hj => by
            change max (u x) 0 * (gradient φ x) i = smoothPositivePart j (u x) * (gradient φ x) i
            rw [hj])))
  have hrightlim : Tendsto
      (fun j => ∫ x, (gradient (fun y => smoothPositivePart j (u y)) x) i * φ x ∂μ)
      atTop (𝓝 (∫ x, (G x) i * φ x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => C * ‖g x i * φ x‖)
    · intro j
      exact (htest j).2.1.1
    · exact hbase.2.1.norm.const_mul C
    · intro j
      exact Eventually.of_forall (fun x => by
        rw [gradient_smoothPositivePart_comp (hu.differentiable (by simp))]
        simp only [PiLp.smul_apply, smul_eq_mul, norm_mul, g]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hboundC j (u x))
          (mul_nonneg (norm_nonneg ((gradient u x) i)) (norm_nonneg (φ x))))
    · exact Eventually.of_forall (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [positivePartSlope_eventually_eq (u x)] with j hj
        rw [gradient_smoothPositivePart_comp (hu.differentiable (by simp)), hj]
        dsimp [G, positivePartGradient, g]
        split_ifs <;> simp)
  refine ⟨hleft, hright, ?_⟩
  have heq : (fun j => ∫ x, smoothPositivePart j (u x) * (gradient φ x) i ∂μ) =
      (fun j => -(∫ x, (gradient (fun y => smoothPositivePart j (u y)) x) i * φ x ∂μ)) :=
    funext (fun j => (htest j).2.2)
  rw [heq] at hleftlim
  exact tendsto_nhds_unique hleftlim hrightlim.neg

end BMCompactPDE
#print axioms BMCompactPDE.positivePartGradient_aestronglyMeasurable
#print axioms BMCompactPDE.positivePartGradient_norm_le
#print axioms BMCompactPDE.hasWeakGradientOn_positivePart_of_contDiff


/-! Actual positive-part W0 membership for smooth compact-support functions.
Neither weak-gradient membership nor a truncation rule is postulated. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

theorem positivePart_zeroBoundarySobolevPair_of_contDiff {n : ℕ} {p : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hSob : SobolevPair p Ω u (gradient u))
    (hcompact : HasCompactSupport (fun x => max (u x) 0))
    (hsupport : tsupport (fun x => max (u x) 0) ⊆ Ω) :
    ZeroBoundarySobolevPair p Ω (fun x => max (u x) 0)
      (positivePartGradient u (gradient u)) := by
  let μ := volume.restrict Ω
  let g := gradient u
  let G := positivePartGradient u g
  let φ : ℕ → Space n → ℝ := fun j x => smoothPositivePart j (u x)
  have hg : Continuous g := BMCompactCapacityV2.continuous_gradient_of_contDiff hu
  have hG : AEStronglyMeasurable G μ :=
    positivePartGradient_aestronglyMeasurable hu.continuous hg μ
  have hmax : AEStronglyMeasurable (fun x => max (u x) 0) μ :=
    (hu.continuous.max continuous_const).aestronglyMeasurable
  have hnormmax (x : Space n) : ‖max (u x) 0‖ ≤ ‖u x‖ := by
    by_cases hx : u x ≤ 0
    · simp [max_eq_right hx]
    · rw [max_eq_left (lt_of_not_ge hx).le]
  have hp : 1 < p := hSob.1
  have huLp : MemLp u (ENNReal.ofReal p) μ := hSob.2.1
  have hgLp : MemLp g (ENNReal.ofReal p) μ := hSob.2.2.1
  have hmaxLp : MemLp (fun x => max (u x) 0) (ENNReal.ofReal p) μ :=
    huLp.of_le hmax (Eventually.of_forall hnormmax)
  have hGLp : MemLp G (ENNReal.ofReal p) μ :=
    hgLp.of_le hG (Eventually.of_forall (positivePartGradient_norm_le u g))
  have hsupp (j : ℕ) : Function.support (φ j) ⊆ Function.support (fun x => max (u x) 0) := by
    intro x hx
    change φ j x ≠ 0 at hx
    change max (u x) 0 ≠ 0
    intro hz
    have hx0 : u x ≤ 0 := (le_max_left (u x) 0).trans hz.le
    exact hx (smoothPositivePart_eq_zero_of_nonpos j hx0)
  have hφ (j : ℕ) : SmoothTest Ω (φ j) := by
    refine ⟨(smoothPositivePart_contDiff j).comp hu, hcompact.mono (hsupp j), ?_⟩
    exact (closure_mono (hsupp j)).trans hsupport
  have hq0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp)
  have hqtop : ENNReal.ofReal p ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  refine ⟨⟨hp, hmaxLp, hGLp, hasWeakGradientOn_positivePart_of_contDiff hu Ω⟩,
    φ, hφ, ?_, ?_⟩
  · apply tendsto_eLpNorm_zero_of_dominated hq0 hqtop
      (b := fun x => (2 : ℝ) • u x)
    · intro j
      exact ((hφ j).1.continuous.aestronglyMeasurable).sub hmax
    · exact huLp.const_smul (2 : ℝ)
    · intro j
      exact Eventually.of_forall (fun x => by
        calc ‖φ j x - max (u x) 0‖ ≤ ‖φ j x‖ + ‖max (u x) 0‖ := norm_sub_le _ _
             _ ≤ ‖u x‖ + ‖u x‖ := add_le_add (smoothPositivePart_norm_le j (u x)) (hnormmax x)
             _ = ‖(2 : ℝ) • u x‖ := by simp [norm_smul]; ring)
    · exact Eventually.of_forall (fun x =>
        tendsto_const_nhds.congr' ((smoothPositivePart_eventually_eq (u x)).mono
          (fun j hj => by dsimp [φ]; rw [hj, sub_self])))
  · obtain ⟨C, hC, hboundC⟩ := positivePartSlope_uniform_bound
    have hC0 : 0 ≤ C := zero_le_one.trans hC
    apply tendsto_eLpNorm_zero_of_dominated hq0 hqtop
      (b := fun x => (C + 1) • g x)
    · intro j
      exact (BMCompactCapacityV2.continuous_gradient_of_contDiff (hφ j).1).aestronglyMeasurable.sub hG
    · exact hgLp.const_smul (C + 1)
    · intro j
      exact Eventually.of_forall (fun x => by
        have hgrad : gradient (φ j) x = positivePartSlope j (u x) • g x :=
          gradient_smoothPositivePart_comp (hu.differentiable (by simp)) j x
        calc ‖gradient (φ j) x - G x‖ ≤ ‖gradient (φ j) x‖ + ‖G x‖ := norm_sub_le _ _
             _ ≤ C * ‖g x‖ + ‖g x‖ := by
               rw [hgrad, norm_smul]
               exact add_le_add (mul_le_mul_of_nonneg_right (hboundC j (u x)) (norm_nonneg _))
                 (positivePartGradient_norm_le u g x)
             _ = ‖(C + 1) • g x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring)
    · exact Eventually.of_forall (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [positivePartSlope_eventually_eq (u x)] with j hj
        rw [gradient_smoothPositivePart_comp (hu.differentiable (by simp)), hj]
        dsimp [G, g, positivePartGradient]
        split_ifs <;> simp)

theorem SmoothTest.positivePart_zeroBoundarySobolevPair {n : ℕ} {p : ℝ}
    (hp : 1 < p) {Ω : Set (Space n)} {u : Space n → ℝ} (hu : SmoothTest Ω u) :
    ZeroBoundarySobolevPair p Ω (fun x => max (u x) 0)
      (positivePartGradient u (gradient u)) := by
  apply positivePart_zeroBoundarySobolevPair_of_contDiff hu.1 (hu.sobolevPair hp)
  · exact hu.2.1.comp_left (g := fun t : ℝ => max t 0) (by simp)
  · exact (tsupport_comp_subset (g := fun t : ℝ => max t 0) (by simp) u).trans hu.2.2

end BMCompactPDE
#print axioms BMCompactPDE.positivePart_zeroBoundarySobolevPair_of_contDiff
#print axioms BMCompactPDE.SmoothTest.positivePart_zeroBoundarySobolevPair


/-! Genuine positive-part comparison for smooth finite-energy solutions with
compact positive-part support inside the domain. The W0 pair is derived from
flat smooth approximations rather than retained as a premise. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

theorem gradient_fun_sub {n : ℕ} {u v : Space n → ℝ}
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v) (x : Space n) :
    gradient (fun y => u y - v y) x = gradient u x - gradient v x := by
  unfold gradient
  rw [fderiv_fun_sub (hu x) (hv x)]
  exact map_sub (InnerProductSpace.toDual ℝ (Space n)).symm _ _

theorem WeakPHarmonicPair.leOn_of_contDiff_compact_positivePart_finiteEnergy
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u v : Space n → ℝ}
    (hu : WeakPHarmonicPair p Ω u (gradient u))
    (hv : WeakPHarmonicPair p Ω v (gradient v))
    (hSu : SobolevPair p Ω u (gradient u))
    (hSv : SobolevPair p Ω v (gradient v))
    (huc : ContDiff ℝ ∞ u) (hvc : ContDiff ℝ ∞ v)
    (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hc : HasCompactSupport (fun x => max (u x - v x) 0))
    (hs : tsupport (fun x => max (u x - v x) 0) ⊆ Ω) :
    ∀ x ∈ Ω, u x ≤ v x := by
  have hcd : ContDiff ℝ ∞ (fun x => u x - v x) := huc.sub hvc
  have hgrad : gradient (fun x => u x - v x) = fun x => gradient u x - gradient v x :=
    funext (gradient_fun_sub (huc.differentiable (by simp)) (hvc.differentiable (by simp)))
  have hSd : SobolevPair p Ω (fun x => u x - v x) (gradient (fun x => u x - v x)) := by
    refine ⟨hu.1, hSu.2.1.sub hSv.2.1, ?_, hasWeakGradientOn_of_contDiff hcd Ω⟩
    rw [hgrad]
    exact hSu.2.2.1.sub hSv.2.2.1
  have hw := positivePart_zeroBoundarySobolevPair_of_contDiff hcd hSd hc hs
  have hpositive : ZeroBoundarySobolevPair p Ω
      (fun x => max (u x - v x) 0)
      (fun x => if v x < u x then gradient u x - gradient v x else 0) := by
    have hG : positivePartGradient (fun x => u x - v x) (gradient (fun x => u x - v x)) =
        (fun x => if v x < u x then gradient u x - gradient v x else 0) := by
      funext x
      change (if 0 < u x - v x then gradient (fun y => u y - v y) x else 0) = _
      rw [hgrad]
      simp only [sub_pos]
    rw [hG] at hw
    exact hw
  exact hu.leOn_of_zeroBoundary_positivePart hv hSu hSv hn hΩb hpositive
    huc.continuous.continuousOn hvc.continuous.continuousOn

theorem WeakPHarmonicPair.leOn_of_contDiff_compact_positivePart
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u v : Space n → ℝ}
    (hu : WeakPHarmonicPair p Ω u (gradient u))
    (hv : WeakPHarmonicPair p Ω v (gradient v))
    (huc : ContDiff ℝ ∞ u) (hvc : ContDiff ℝ ∞ v)
    (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hc : HasCompactSupport (fun x => max (u x - v x) 0))
    (hs : tsupport (fun x => max (u x - v x) 0) ⊆ Ω) :
    ∀ x ∈ Ω, u x ≤ v x := by
  have hD : LocalDomain Ω (Set.univ : Set (Space n)) :=
    ⟨hu.2.1, hΩb, subset_univ _⟩
  have hSu := sobolevPair_of_contDiffOn hu.1 isOpen_univ huc.contDiffOn hD
  have hSv := sobolevPair_of_contDiffOn hv.1 isOpen_univ hvc.contDiffOn hD
  exact hu.leOn_of_contDiff_compact_positivePart_finiteEnergy hv hSu hSv huc hvc hn hΩb hc hs

end BMCompactPDE
#print axioms BMCompactPDE.gradient_fun_sub
#print axioms BMCompactPDE.WeakPHarmonicPair.leOn_of_contDiff_compact_positivePart_finiteEnergy
#print axioms BMCompactPDE.WeakPHarmonicPair.leOn_of_contDiff_compact_positivePart

