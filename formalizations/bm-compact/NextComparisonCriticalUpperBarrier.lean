import NextComparisonCriticalBarrier

/-! Actual critical upper-barrier sequences around an exterior tangent ball.
Translation and complementation of the genuine finite-logarithmic lower family
give global nonnegativity and unit lower values past any prescribed separated
radius. The scalar and true weak-gradient equation are both constructed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

theorem exists_smooth_critical_exterior_tangent_upper_barrier_sequence
    {n : ℕ} (hn : 2≤n) (z : Space n) {r L : ℝ} (hr : 0<r) (hrL : r<L)
    {a : Space n} (ha : dist a z=r) :
    ∃ W : ℕ → Space n → ℝ,(∀ j,ContDiff ℝ ∞ (W j)) ∧
      (∀ j x,0≤W j x) ∧ (∀ j x,L≤dist x z → 1≤W j x) ∧
      (∀ j,WeakPHarmonicPair (n : ℝ) (closedBall z r)ᶜ (W j) (gradient (W j))) ∧
      Tendsto (fun j=>W j a) atTop (𝓝 0) := by
  have ha0 : dist (a-z) (0 : Space n)=r := by
    simpa only [dist_zero_right,dist_eq_norm,sub_zero] using ha
  obtain ⟨B,hBc,hB1,hBout,hBH,hBa⟩ :=
    exists_smooth_critical_finite_ball_barrier_sequence hn (0 : Space n) hr
      (by simpa only [norm_zero,zero_add] using hrL) ha0
  let W : ℕ → Space n → ℝ := fun j x=>-B j (x-z)+1
  have hWc (j : ℕ) : ContDiff ℝ ∞ (W j) :=
    ((hBc j).comp (contDiff_id.sub contDiff_const)).neg.add contDiff_const
  have hW0 (j : ℕ) (x : Space n) : 0≤W j x := by
    dsimp only [W]
    linarith only [hB1 j (x-z)]
  have hW1 (j : ℕ) (x : Space n) (hx : L≤dist x z) : 1≤W j x := by
    have hout : x-z∉ball (0 : Space n) L := by
      simpa only [mem_ball,dist_zero_right,dist_eq_norm,sub_zero,not_lt] using hx
    have hb := hBout j (x-z) hout
    dsimp only [W]
    linarith only [hb]
  have hWH (j : ℕ) : WeakPHarmonicPair (n : ℝ) (closedBall z r)ᶜ (W j) (gradient (W j)) := by
    have ht := (((hBH j).smul (-1)).add_const 1).source_zero.translate_actual (-z)
    have hdom : (fun x : Space n=>x+(-z)) ⁻¹' (closedBall (0 : Space n) r)ᶜ=(closedBall z r)ᶜ := by
      ext x
      simp only [mem_preimage,mem_compl_iff,mem_closedBall,dist_eq_norm,sub_eq_add_neg,neg_zero,add_zero]
    rw [hdom] at ht
    have hu : WeakPHarmonicPair (n : ℝ) (closedBall z r)ᶜ (W j)
        (fun x=>-gradient (B j) (x-z)) := by
      simpa only [W,Pi.smul_apply,smul_eq_mul,neg_one_mul,neg_one_smul,sub_eq_add_neg] using ht.harmonic_of_source_zero
    apply hu.congr_gradient_on
    intro x _
    have hneg : gradient (W j) x=-gradient (fun y=>B j (y-z)) x := by
      dsimp only [W]
      unfold gradient
      rw [fderiv_add_const,fderiv_fun_neg,map_neg]
    rw [hneg]
    have hcomp : gradient (fun y=>B j (y-z)) x=gradient (B j) (x-z) := by
      simpa only [sub_eq_add_neg] using gradient_comp_add_actual (B j) (-z) x
    exact congrArg Neg.neg hcomp.symm
  refine ⟨W,hWc,hW0,hW1,hWH,?_⟩
  have hh := hBa.neg.add_const 1
  simpa only [W,neg_add_cancel] using hh

end BMCompactPDE
#print axioms BMCompactPDE.exists_smooth_critical_exterior_tangent_upper_barrier_sequence
