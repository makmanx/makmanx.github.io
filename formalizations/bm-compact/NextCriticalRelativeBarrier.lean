import UpstreamBoundaryExcess
import WeakPositivePartComparison

/-! Bounded-domain lower-barrier comparison from genuine relative-capacity
admissible data. Strict positive superlevels lie compactly inside the outer
open set because the smooth barrier is nonpositive outside. The actual W0
obstacle excess is constructed, with no obstacle trace or boundary C0 input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1400000 in
theorem WeakPHarmonicPair.smooth_lower_barrier_le_on_bounded_relative_admissible_data
    {n : ℕ} {p : ℝ} {K O : Set (Space n)} (hK : IsCompact K) (hn : 2≤n)
    (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p (O\K) u g) (huc : ContinuousOn u (O\K))
    (hSob : SobolevPair p O u g) (hu0 : ∀ᵐ x ∂volume.restrict O,0≤u x)
    {φ : ℕ → Space n → ℝ} (hφ : ∀ j,BMCompactCapacityV2.Admissible K O (φ j))
    (hlimu : Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0))
    (hlimg : Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0))
    {b : Space n → ℝ} (hb : ContDiff ℝ ∞ b) (hbK : ∀ x∈K,b x≤1)
    (hbH : WeakPHarmonicPair p (O\K) b (gradient b))
    (hbOut : ∀ x∉O,b x≤0) : ∀ x∈O\K,b x≤u x := by
  have hφU (j : ℕ) : BMCompactCapacityV2.Admissible K univ (φ j) :=
    ⟨(hφ j).1,(hφ j).2.1,subset_univ _,(hφ j).2.2.2⟩
  have hp : 0<p := zero_lt_one.trans hu.1
  have heps (x : Space n) (hx : x∈O\K) (ε : ℝ) (hε : 0<ε) : b x-ε≤u x := by
    let E : Set (Space n) := {y | ε≤b y}
    have hEclosed : IsClosed E := isClosed_le continuous_const hb.continuous
    have hEO : E⊆O := by
      intro y hy
      by_contra hyn
      have hh := hbOut y hyn
      change ε≤b y at hy
      linarith only [hh,hy,hε]
    have hE : IsCompact E := hOb.isCompact_closure.of_isClosed_subset hEclosed
      (hEO.trans subset_closure)
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
    have hw := capacity_admissible_local_excess_zeroBoundary hO hSob hφU hlimu hlimg hχ hχ0 hb hbK hε
    let D := O\K
    have hD : IsOpen D := hO.sdiff hK.isClosed
    have hDb : Bornology.IsBounded D := hOb.subset sdiff_subset
    let v : Space n → ℝ := fun y=>b y+(-ε)
    have htest : ZeroBoundarySobolevPair p D (fun y=>max (v y-u y) 0)
        (fun y=>if u y<v y then gradient b y-g y else 0) := by
      apply hw.congr
      · filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset hu0] with y hy
        by_cases hd : u y<v y
        · have hyb : ε<b y := by dsimp only [v] at hd;linarith only [hd,hy]
          rw [hχE y hyb.le,one_mul]
          congr 1
          dsimp only [v]
          ring
        · have hd0 : b y-u y-ε≤0 := by dsimp only [v] at hd;linarith only [le_of_not_gt hd]
          have hcut0 : χ y*(b y-u y-ε)≤0 := mul_nonpos_of_nonneg_of_nonpos (hχ0 y) hd0
          rw [max_eq_right hcut0,max_eq_right (sub_nonpos.mpr (le_of_not_gt hd))]
      · filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset hu0] with y hy
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
    have hbu : WeakPHarmonicPair p D v (gradient b) := hbH.add_const (-ε)
    have huu : WeakPHarmonicPair p D u g := hu
    have hSb : SobolevPair p D v (gradient b) := by
      have hs := sobolevPair_of_contDiffOn_one hu.1 isOpen_univ
        (((hb.add contDiff_const).of_le (by simp) : ContDiff ℝ 1 v).contDiffOn)
        (show LocalDomain D univ from ⟨hD,hDb,subset_univ _⟩)
      have heq : gradient v=gradient b := funext (fun y=>BMCompactAnalytic.gradient_add_const b (-ε) y)
      rwa [heq] at hs
    exact hbu.leOn_of_zeroBoundary_positivePart huu hSb (hSob.mono_actual sdiff_subset) hn hDb htest
      (hb.continuous.add continuous_const).continuousOn huc x hx
  intro x hx
  by_contra hnot
  have hε : 0<(b x-u x)/2 := by linarith only [lt_of_not_ge hnot]
  have he := heps x hx ((b x-u x)/2) hε
  linarith only [he,lt_of_not_ge hnot]

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.smooth_lower_barrier_le_on_bounded_relative_admissible_data
