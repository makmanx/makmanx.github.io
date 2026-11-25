import UpstreamBoundaryExcess
import WeakPositivePartComparison

/-! Actual lower-barrier comparison for variational capacitary data.
The obstacle W0 excess is constructed from admissible approximants, and the
local PDE is extended to whole-domain W0 tests by actual Sobolev density.
No boundary value or boundary-continuous representative is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem upstream_local_Lp_limit_of_global {n : ℕ} {p q : ℝ}
    (hp : 0<p) (hpq : p≤q) {O : Set (Space n)} (hOb : Bornology.IsBounded O)
    {f : ℕ → Space n → ℝ} (hf : ∀ j,AEStronglyMeasurable (f j) volume)
    (hlim : Tendsto (fun j=>eLpNorm (f j) (ENNReal.ofReal q) volume) atTop (𝓝 0)) :
    Tendsto (fun j=>eLpNorm (f j) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) := by
  have hq : 0<q := hp.trans_le hpq
  have hr : 0≤1/p-1/q := sub_nonneg.mpr (one_div_le_one_div_of_le hp hpq)
  let C : ℝ≥0∞ := (volume O)^(1/p-1/q)
  have hC : C≠(∞:ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg hr hOb.measure_lt_top.ne
  have hloc : Tendsto (fun j=>eLpNorm (f j) (ENNReal.ofReal q) (volume.restrict O)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _=>bot_le)
      (fun _=>eLpNorm_mono_measure _ Measure.restrict_le_self)
  have ht := ENNReal.Tendsto.const_mul hloc (Or.inr hC)
  simp only [mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _=>bot_le)
  intro j
  have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ:=volume.restrict O) (ENNReal.ofReal_le_ofReal hpq) ((hf j).restrict)
  simpa only [ENNReal.toReal_ofReal hp.le,ENNReal.toReal_ofReal hq.le,Measure.restrict_apply_univ,mul_comm,C] using he

set_option maxHeartbeats 1400000 in
theorem WeakPHarmonicPair.smooth_lower_barrier_le_of_admissible_approximation
    {n : ℕ} {p q : ℝ} {K : Set (Space n)} (hK : IsCompact K) (hn : 2≤n)
    (hpq : p≤q) {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Kᶜ u g) (huc : ContinuousOn u Kᶜ)
    (hSob : ∀ O : Set (Space n),Bornology.IsBounded O → SobolevPair p O u g)
    (huq : MemLp u (ENNReal.ofReal q) volume) (hu0 : ∀ᵐ x ∂volume,0≤u x)
    {φ : ℕ → Space n → ℝ} (hφ : ∀ j,BMCompactCapacityV2.Admissible K univ (φ j))
    (hlimu : Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal q) volume) atTop (𝓝 0))
    (hlimg : Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0))
    {b : Space n → ℝ} (hb : ContDiff ℝ ∞ b) (hbK : ∀ x∈K,b x≤1)
    (hbH : WeakPHarmonicPair p Kᶜ b (gradient b))
    (hbinfty : Tendsto b (cocompact (Space n)) (𝓝 0)) :
    ∀ x∈Kᶜ,b x≤u x := by
  have hp : 0<p := zero_lt_one.trans hu.1
  have hφm (j : ℕ) : MemLp (φ j) (ENNReal.ofReal q) volume :=
    BMCompactCapacityV2.smooth_compactSupport_memLp _ (hφ j).1 (hφ j).2.1
  have heps (x : Space n) (hx : x∈Kᶜ) (ε : ℝ) (hε : 0<ε) : b x-ε≤u x := by
    let E : Set (Space n) := {y | ε≤b y}
    have hEclosed : IsClosed E := isClosed_le continuous_const hb.continuous
    have htail : {y | b y<ε}∈cocompact (Space n) := hbinfty.eventually (eventually_lt_nhds hε)
    obtain ⟨T,hT,hET⟩ := mem_cocompact'.mp htail
    have hE : IsCompact E := hT.of_isClosed_subset hEclosed (by
      intro y hy
      apply hET
      change ε≤b y at hy
      change ¬b y<ε
      exact not_lt.mpr hy)
    let O : Set (Space n) := thickening 1 (E∪{x})
    have hO : IsOpen O := isOpen_thickening
    have hOb : Bornology.IsBounded O := (hE.union isCompact_singleton).isBounded.thickening
    have hEO : E⊆O := (subset_union_left : E⊆E∪{x}).trans (self_subset_thickening (by norm_num) _)
    have hxO : x∈O := self_subset_thickening (by norm_num) (E∪{x}) (Or.inr rfl)
    obtain ⟨a,ha⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hE hO hEO
    let χ : Space n → ℝ := fun y=>Real.smoothTransition (a y)
    have hχ : SmoothTest O χ := ⟨Real.smoothTransition.contDiff.comp ha.1,
      ha.2.1.comp_left (Real.smoothTransition.zero_of_nonpos le_rfl),
      (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos le_rfl) a).trans ha.2.2.1⟩
    have hχ0 (y : Space n) : 0≤χ y := Real.smoothTransition.nonneg _
    have hχE (y : Space n) (hy : y∈E) : χ y=1 :=
      Real.smoothTransition.one_of_one_le (ha.2.2.2 y hy)
    have hχnear (y : Space n) (hy : ε<b y) : χ=ᶠ[𝓝 y] (fun _=>(1:ℝ)) := by
      have ht := hb.continuous.continuousAt.tendsto.eventually (eventually_gt_nhds hy)
      filter_upwards [ht] with z hz
      exact hχE z hz.le
    have hgradχ (y : Space n) (hy : ε<b y) : gradient χ y=0 := by
      unfold gradient
      rw [(hχnear y hy).fderiv_eq]
      simp
    have hgradγ (y : Space n) (hy : ε<b y) :
        gradient (fun z=>χ z*(b z-ε)) y=gradient b y := by
      have heq : (fun z=>χ z*(b z-ε))=ᶠ[𝓝 y] (fun z=>b z-ε) := by
        filter_upwards [hχnear y hy] with z hz
        rw [hz,one_mul]
      have hg : gradient (fun z=>χ z*(b z-ε)) y=gradient (fun z=>b z-ε) y := by
        unfold gradient
        rw [heq.fderiv_eq]
      exact hg.trans (by simpa only [sub_eq_add_neg] using BMCompactAnalytic.gradient_add_const b (-ε) y)
    have hlocalu := upstream_local_Lp_limit_of_global hp hpq hOb
      (fun j=>((hφm j).sub huq).1) hlimu
    have hlocalg : Tendsto (fun j=>eLpNorm (fun y=>gradient (φ j) y-g y)
        (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimg (fun _=>bot_le)
        (fun _=>eLpNorm_mono_measure _ Measure.restrict_le_self)
    have hw := capacity_admissible_local_excess_zeroBoundary hO (hSob O hOb) hφ hlocalu hlocalg hχ hχ0 hb hbK hε
    let D := O\K
    have hD : IsOpen D := hO.sdiff hK.isClosed
    have hDb : Bornology.IsBounded D := hOb.subset sdiff_subset
    have hDK : D⊆Kᶜ := fun _ hy=>hy.2
    let v : Space n → ℝ := fun y=>b y+(-ε)
    have htest : ZeroBoundarySobolevPair p D (fun y=>max (v y-u y) 0)
        (fun y=>if u y<v y then gradient b y-g y else 0) := by
      apply hw.congr
      · filter_upwards [ae_restrict_of_ae hu0] with y hy
        by_cases hd : u y<v y
        · have hyb : ε<b y := by dsimp only [v] at hd;linarith only [hd,hy]
          rw [hχE y hyb.le,one_mul]
          congr 1
          dsimp only [v]
          ring
        · have hd0 : b y-u y-ε≤0 := by dsimp only [v] at hd;linarith only [le_of_not_gt hd]
          have hcut0 : χ y*(b y-u y-ε)≤0 := mul_nonpos_of_nonneg_of_nonpos (hχ0 y) hd0
          rw [max_eq_right hcut0,max_eq_right (sub_nonpos.mpr (le_of_not_gt hd))]
      · filter_upwards [ae_restrict_of_ae hu0] with y hy
        by_cases hd : u y<v y
        · have hyb : ε<b y := by dsimp only [v] at hd;linarith only [hd,hy]
          have hpos : 0<χ y*(b y-u y-ε) := by rw [hχE y hyb.le,one_mul];dsimp only [v] at hd;linarith only [hd]
          change (if 0<χ y*(b y-u y-ε) then
            gradient (fun z=>χ z*(b z-ε)) y-(χ y • g y+u y • gradient χ y) else 0)=_
          rw [if_pos hpos,if_pos hd]
          simp only [hgradγ y hyb,hχE y hyb.le,hgradχ y hyb,one_smul,smul_zero,add_zero]
        · have hd0 : b y-u y-ε≤0 := by dsimp only [v] at hd;linarith only [le_of_not_gt hd]
          have hcut0 : χ y*(b y-u y-ε)≤0 := mul_nonpos_of_nonneg_of_nonpos (hχ0 y) hd0
          simp only [positivePartGradient,if_neg (not_lt.mpr hcut0),if_neg hd]
    have hbu : WeakPHarmonicPair p D v (gradient b) := (hbH.add_const (-ε)).mono hDK hD
    have huu : WeakPHarmonicPair p D u g := hu.mono hDK hD
    have hSb : SobolevPair p D v (gradient b) := by
      have hs := sobolevPair_of_contDiffOn_one hu.1 isOpen_univ
        (((hb.add contDiff_const).of_le (by simp) : ContDiff ℝ 1 v).contDiffOn)
        (show LocalDomain D univ from ⟨hD,hDb,subset_univ _⟩)
      have heq : gradient v=gradient b := funext (fun y=>BMCompactAnalytic.gradient_add_const b (-ε) y)
      rwa [heq] at hs
    exact hbu.leOn_of_zeroBoundary_positivePart huu hSb (hSob D hDb) hn hDb htest
      (hb.continuous.add continuous_const).continuousOn (huc.mono hDK) x ⟨hxO,hx⟩
  intro x hx
  by_contra hnot
  have hε : 0<(b x-u x)/2 := by linarith only [lt_of_not_ge hnot]
  have he := heps x hx ((b x-u x)/2) hε
  linarith only [he,lt_of_not_ge hnot]

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.smooth_lower_barrier_le_of_admissible_approximation
