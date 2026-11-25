import NextCriticalW0Localization
import NextRootSobolevIdeal
import WeakPositivePartComparison

/-! Actual upper-barrier comparison for bounded relative capacitary data.
The outer W0 graph and genuine Sobolev ideal bridge give the strict excess.
The unit bound and smooth upper barrier kill it in a neighborhood of K; an
actual off-K W0 localization supplies the full PDE test. No trace is input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1400000 in
theorem WeakPHarmonicPair.smooth_upper_barrier_ge_of_actual_zeroBoundary_data
    {n : ℕ} {p : ℝ} {K O : Set (Space n)} (hK : IsCompact K) (hn : 2≤n)
    (hO : IsOpen O) (hKO : K⊆O) (hOb : Bornology.IsBounded O)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p (O\K) u g) (huc : ContinuousOn u (O\K))
    (huW : ZeroBoundarySobolevPair p O u g) (hu1 : ∀ᵐ x ∂volume.restrict O,u x≤1)
    {b : Space n → ℝ} (hb : ContDiff ℝ ∞ b) (hbK : ∀ x∈K,1≤b x)
    (hb0 : ∀ x∈O,0≤b x) (hbH : WeakPHarmonicPair p (O\K) b (gradient b)) :
    ∀ x∈O\K,u x≤b x := by
  have hD : IsOpen (O\K) := hO.sdiff hK.isClosed
  have hDb : Bornology.IsBounded (O\K) := hOb.subset sdiff_subset
  have hSb : SobolevPair p O b (gradient b) := sobolevPair_of_contDiffOn_one hu.1 isOpen_univ
    ((hb.of_le (by simp) : ContDiff ℝ 1 b).contDiffOn) ⟨hO,hOb,subset_univ _⟩
  have heps (ε : ℝ) (hε : 0<ε) : ∀ x∈O\K,u x≤b x+ε := by
    have htestO := ZeroBoundarySobolevPair.positivePart_sub_nonnegative_sobolev hO hOb huW hSb hb0 hε.le
    let N : Set (Space n) := {x | 1-ε/2<b x}
    have hN : IsOpen N := isOpen_lt continuous_const hb.continuous
    have hKN : K⊆N := by
      intro x hx
      have hh := hbK x hx
      change 1-ε/2<b x
      linarith only [hh,hε]
    have hz : ∀ᵐ x ∂volume.restrict O,x∈N →
        max (u x-b x-ε) 0=0 ∧ positivePartGradient (fun y=>u y-b y-ε) (g-gradient b) x=0 := by
      filter_upwards [hu1] with x hx hxN
      have hh : 1-ε/2<b x := hxN
      have hs : u x-b x-ε≤0 := by linarith only [hx,hh,hε]
      refine ⟨max_eq_right hs,?_⟩
      exact if_neg (not_lt.mpr hs)
    have htestK := ZeroBoundarySobolevPair.off_compact_of_zero_on_open_neighborhood
      hO hK hKO hN hKN htestO hz
    let v : Space n → ℝ := fun x=>b x+ε
    have htest : ZeroBoundarySobolevPair p (O\K) (fun x=>max (u x-v x) 0)
        (fun x=>if v x<u x then g x-gradient b x else 0) := by
      apply htestK.congr
      · exact Eventually.of_forall (fun x=>by dsimp only [v];congr 1;ring)
      · exact Eventually.of_forall (fun x=>by
          change (if 0<u x-b x-ε then g x-gradient b x else 0)=_
          have he : (0<u x-b x-ε) ↔ v x<u x := by dsimp only [v];constructor <;> intro hh <;> linarith only [hh]
          simp only [he])
    have hSv : SobolevPair p (O\K) v (gradient b) := by
      have hs := (hSb.mono_actual (sdiff_subset : O\K⊆O)).add (sobolevPair_const hu.1 hDb ε)
      exact hs.congr (Eventually.of_forall (fun x=>rfl)) (Eventually.of_forall (fun x=>by simp))
    exact hu.leOn_of_zeroBoundary_positivePart (hbH.add_const ε)
      (huW.1.mono_actual sdiff_subset) hSv hn hDb htest huc (hb.continuous.add continuous_const).continuousOn
  intro x hx
  by_contra hnot
  have hε : 0<(u x-b x)/2 := by linarith only [lt_of_not_ge hnot]
  have hh := heps ((u x-b x)/2) hε x hx
  linarith only [hh,lt_of_not_ge hnot]

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.smooth_upper_barrier_ge_of_actual_zeroBoundary_data
