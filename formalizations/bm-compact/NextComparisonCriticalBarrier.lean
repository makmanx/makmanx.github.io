import BMCompactChecked
import GradientAnalyticBatch

/-! Genuine smooth finite-outer-ball logarithmic lower barriers at p=n.
The flattening transition is strictly inside the inner tangent ball. Actual
weak n-harmonicity is proved outside that ball; the barriers are nonpositive
outside the specified finite outer ball. No trace, comparison, infinity-decay
or barrier-family hypothesis is supplied. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem next_critical_gradient_sub {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (z x : Space n) :
    gradient (fun y=>f (y-z)) x=gradient f (x-z) := by
  have hd : HasFDerivAt (fun y=>f (y-z)) (fderiv ℝ f (x-z)) x := by
    convert! (hf.differentiable (by simp) (x-z)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const z) using 1 <;> simp
  unfold gradient
  rw [hd.fderiv]

private theorem next_critical_fixed_barrier {n : ℕ} (hn : 1<(n : ℝ))
    (z : Space n) {r R s : ℝ} (hs : 0<s) (hsr : s<r) (hsep : ‖z‖+r<R) :
    ∃ B : Space n → ℝ,ContDiff ℝ ∞ B ∧ (∀ x,B x≤1) ∧
      (∀ x,x∉ball (0 : Space n) R → B x≤0) ∧
      WeakPHarmonicPair (n : ℝ) (closedBall z r)ᶜ B (gradient B) ∧
      ∀ a : Space n,dist a z=r → B a=
        (fundamentalRadialValue n 1 (n : ℝ) (R-‖z‖)-fundamentalRadialValue n 1 (n : ℝ) r)/
        (fundamentalRadialValue n 1 (n : ℝ) (R-‖z‖)-fundamentalRadialValue n 1 (n : ℝ) s) := by
  let L : ℝ := R-‖z‖
  have hr : 0<r := hs.trans hsr
  have hrL : r<L := by dsimp only [L];linarith only [hsep]
  have hL : 0<L := hr.trans hrL
  let d : ℝ := fundamentalRadialValue n 1 (n : ℝ) L-fundamentalRadialValue n 1 (n : ℝ) s
  have hd : 0<d := sub_pos.mpr
    (strictMonoOn_fundamentalRadialValue_all_p n zero_lt_one hn hs hL (hsr.trans hrL))
  let A : ℝ := fundamentalRadialValue n 1 (n : ℝ) L/d
  let C : ℝ := -d⁻¹
  let b : ContDiffBump (0 : Space n) := ⟨s,(s+r)/2,hs,by linarith only [hsr]⟩
  have hbr : b.rOut<r := by dsimp only [b];linarith only [hsr]
  let B : Space n → ℝ := fun x=>b (x-z)+A*(1-b (x-z))+C*flattenedRadialPrimitive n (n : ℝ) b (x-z)
  have hf := contDiff_flattenedRadialPrimitive n (n : ℝ) b
  have hBc : ContDiff ℝ ∞ B :=
    ((b.contDiff.comp (contDiff_id.sub contDiff_const)).add
      (contDiff_const.mul (contDiff_const.sub (b.contDiff.comp (contDiff_id.sub contDiff_const))))).add
      (contDiff_const.mul (hf.comp (contDiff_id.sub contDiff_const)))
  have hblend (x : Space n) : B x=b (x-z)+(1-b (x-z))*
      ((fundamentalRadialValue n 1 (n : ℝ) L-fundamentalPotential n 1 (n : ℝ) (x-z))/d) := by
    dsimp only [B,A,C,flattenedRadialPrimitive]
    ring
  have hradial (x : Space n) (hx : b.rOut≤‖x-z‖) :
      B x=(fundamentalRadialValue n 1 (n : ℝ) L-fundamentalPotential n 1 (n : ℝ) (x-z))/d := by
    rw [hblend,b.zero_of_le_dist (by simpa only [dist_zero_right] using hx)]
    ring
  have hB1 (x : Space n) : B x≤1 := by
    by_cases hx : ‖x-z‖≤s
    · have hb : b (x-z)=1 := b.one_of_mem_closedBall
        (by simpa only [mem_closedBall,dist_zero_right] using hx)
      rw [hblend,hb]
      ring_nf
      exact le_rfl
    · have hxs : s<‖x-z‖ := lt_of_not_ge hx
      have hm : fundamentalRadialValue n 1 (n : ℝ) s≤fundamentalPotential n 1 (n : ℝ) (x-z) := by
        rw [←fundamentalPotential_norm]
        exact (strictMonoOn_fundamentalRadialValue_all_p n zero_lt_one hn).monotoneOn
          hs (hs.trans hxs) hxs.le
      have hprof : (fundamentalRadialValue n 1 (n : ℝ) L-fundamentalPotential n 1 (n : ℝ) (x-z))/d≤1 := by
        apply (div_le_one hd).mpr
        dsimp only [d]
        linarith only [hm]
      rw [hblend]
      have hh := mul_nonneg (sub_nonneg.mpr (b.le_one (x:=x-z))) (sub_nonneg.mpr hprof)
      nlinarith only [hh]
  have hBout (x : Space n) (hx : x∉ball (0 : Space n) R) : B x≤0 := by
    have hRx : R≤‖x‖ := le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hx)
    have ht := norm_add_le (x-z) z
    rw [sub_add_cancel] at ht
    have hLx : L≤‖x-z‖ := by dsimp only [L];linarith only [ht,hRx]
    have hm : fundamentalRadialValue n 1 (n : ℝ) L≤fundamentalPotential n 1 (n : ℝ) (x-z) := by
      rw [←fundamentalPotential_norm]
      exact (strictMonoOn_fundamentalRadialValue_all_p n zero_lt_one hn).monotoneOn
        hL (hL.trans_le hLx) hLx
    rw [hradial x (hbr.le.trans (hrL.le.trans hLx))]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hm) hd.le
  let O : Set (Space n) := (closedBall z r)ᶜ
  have hO : IsOpen O := isClosed_closedBall.isOpen_compl
  have hOx {x : Space n} (hx : x∈O) : b.rOut<‖x-z‖ := by
    have hh : r<dist x z := lt_of_not_ge hx
    exact hbr.trans (by simpa only [dist_eq_norm] using hh)
  have ht := (((weakPHarmonicPair_flattenedRadialPrimitive n hn b).smul C).add_const A).source_zero.translate_actual (-z)
  have hu : WeakPHarmonicPair (n : ℝ) {x : Space n | b.rOut<‖x-z‖}
      (fun x=>C*flattenedRadialPrimitive n (n : ℝ) b (x-z)+A)
      (fun x=>C • gradient (flattenedRadialPrimitive n (n : ℝ) b) (x-z)) := by
    simpa only [Pi.smul_apply,smul_eq_mul,sub_eq_add_neg,preimage_setOf_eq] using ht.harmonic_of_source_zero
  have heq : EqOn (fun x=>C*flattenedRadialPrimitive n (n : ℝ) b (x-z)+A) B O := by
    intro x hx
    have hb : b (x-z)=0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using (hOx hx).le)
    dsimp only [B]
    rw [hb]
    ring
  have hweak : WeakPHarmonicPair (n : ℝ) O B (gradient B) := by
    apply ((hu.mono (fun x hx=>hOx hx) hO).congr_fun heq).congr_gradient_on
    intro x hx
    have he : (fun y=>C*flattenedRadialPrimitive n (n : ℝ) b (y-z)+A)=ᶠ[𝓝 x] B := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact heq hy
    calc
      C • gradient (flattenedRadialPrimitive n (n : ℝ) b) (x-z)=
          gradient (fun y=>C*flattenedRadialPrimitive n (n : ℝ) b (y-z)+A) x := by
        have hadd : gradient (fun y=>C*flattenedRadialPrimitive n (n : ℝ) b (y-z)+A) x=
            gradient (fun y=>C*flattenedRadialPrimitive n (n : ℝ) b (y-z)) x := by
          unfold gradient
          rw [fderiv_add_const]
        rw [hadd,BMCompactCapacityV2.gradient_const_mul,next_critical_gradient_sub hf]
      _=gradient B x := he.gradient_eq
  refine ⟨B,hBc,hB1,hBout,hweak,?_⟩
  intro a ha
  rw [hradial a (hbr.le.trans (by simpa only [dist_eq_norm] using ha.ge)),
    ←fundamentalPotential_norm,show ‖a-z‖=r by simpa only [dist_eq_norm] using ha]

/-- Critical logarithmic barriers for a genuine interior tangent ball in a
finite outer ball. Every function and its true weak equation is constructed. -/
theorem exists_smooth_critical_finite_ball_barrier_sequence {n : ℕ}
    (hn : 2≤n) (z : Space n) {r R : ℝ} (hr : 0<r) (hsep : ‖z‖+r<R)
    {a : Space n} (ha : dist a z=r) :
    ∃ B : ℕ → Space n → ℝ,(∀ j,ContDiff ℝ ∞ (B j)) ∧ (∀ j x,B j x≤1) ∧
      (∀ j x,x∉ball (0 : Space n) R → B j x≤0) ∧
      (∀ j,WeakPHarmonicPair (n : ℝ) (closedBall z r)ᶜ (B j) (gradient (B j))) ∧
      Tendsto (fun j=>B j a) atTop (𝓝 1) := by
  classical
  have hnR : 1<(n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2) hn)
  let s : ℕ → ℝ := fun j=>r*((j : ℝ)+1)/((j : ℝ)+2)
  have hs (j : ℕ) : 0<s j := div_pos (mul_pos hr (by positivity)) (by positivity)
  have hsr (j : ℕ) : s j<r := by
    dsimp only [s]
    apply (div_lt_iff₀ (by positivity : 0<(j : ℝ)+2)).mpr
    nlinarith only [hr]
  choose B hBc hB1 hBout hBH hBa using (fun j=>next_critical_fixed_barrier hnR z (hs j) (hsr j) hsep)
  refine ⟨B,hBc,hB1,hBout,hBH,?_⟩
  have hinv : Tendsto (fun j : ℕ=>((j : ℝ)+2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hsLim : Tendsto s atTop (𝓝 r) := by
    have hh := ((tendsto_const_nhds (x:=(1 : ℝ))).sub hinv).const_mul r
    simp only [sub_zero,mul_one] at hh
    apply hh.congr'
    exact Eventually.of_forall (fun j=>by dsimp only [s];field_simp <;> ring)
  have hFc : ContinuousAt (fundamentalRadialValue n 1 (n : ℝ)) r :=
    (contDiffAt_fundamentalPotential n 1 (n : ℝ) hr.ne').continuousAt
  have hFr : Tendsto (fun j=>fundamentalRadialValue n 1 (n : ℝ) (s j))
      atTop (𝓝 (fundamentalRadialValue n 1 (n : ℝ) r)) := hFc.tendsto.comp hsLim
  have hL : r<R-‖z‖ := by linarith only [hsep]
  have hd : 0<fundamentalRadialValue n 1 (n : ℝ) (R-‖z‖)-fundamentalRadialValue n 1 (n : ℝ) r :=
    sub_pos.mpr (strictMonoOn_fundamentalRadialValue_all_p n zero_lt_one hnR hr (hr.trans hL) hL)
  have hh := (tendsto_const_nhds (x:=fundamentalRadialValue n 1 (n : ℝ) (R-‖z‖)-
      fundamentalRadialValue n 1 (n : ℝ) r)).div ((tendsto_const_nhds).sub hFr) hd.ne'
  rw [div_self hd.ne'] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun j=>(hBa j a ha).symm)

end BMCompactPDE
#print axioms BMCompactPDE.exists_smooth_critical_finite_ball_barrier_sequence
