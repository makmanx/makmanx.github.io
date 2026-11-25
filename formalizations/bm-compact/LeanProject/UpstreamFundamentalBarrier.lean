import BMCompactChecked
import GradientAnalyticBatch
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Explicit globally smooth lower-barrier sequences for an interior tangent
ball,1<p<n. Their transition lies strictly inside the ball;the actual full-W0
p-Laplace equation outside the ball and the two genuine limits are proved.
No boundary trace,comparison or barrier-family premise is supplied. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem barrier_coefficient_normalizes {n : ℕ} {p s : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) (hs : 0<s) :
    (((p-(n : ℝ))/(p-1))*s^(-((p-(n : ℝ))/(p-1))))*
      fundamentalRadialValue n 1 p s = 1 := by
  let q : ℝ := (p-(n : ℝ))/(p-1)
  have hq : q≠0 := ne_of_lt (div_neg_of_neg_of_pos (sub_neg.mpr hpn) (sub_pos.mpr hp))
  have hf : fundamentalRadialValue n 1 p s=q⁻¹*s^q := by
    simp only [fundamentalRadialValue,fundamentalPotential,if_neg (ne_of_lt hpn),
      radialPowerPotential,Real.one_rpow,mul_one,Real.norm_eq_abs,abs_of_pos hs]
    rfl
  rw [hf]
  change (q*s^(-q))*(q⁻¹*s^q)=1
  calc
    _=(q*q⁻¹)*(s^(-q)*s^q) := by ring
    _=1 := by rw [mul_inv_cancel₀ hq,←Real.rpow_add hs];simp

private theorem barrier_gradient_sub {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (z x : Space n) :
    gradient (fun y => f (y-z)) x=gradient f (x-z) := by
  have hd : HasFDerivAt (fun y => f (y-z)) (fderiv ℝ f (x-z)) x := by
    convert! (hf.differentiable (by simp) (x-z)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const z) using 1 <;> simp
  unfold gradient
  rw [hd.fderiv]

private theorem exists_smooth_fixed_ball_barrier {n : ℕ} {p R s : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) (z : Space n) (hs : 0<s) (hsR : s<R) :
    ∃ B : Space n → ℝ,ContDiff ℝ ∞ B ∧ (∀ x,B x≤1) ∧
      WeakPHarmonicPair p (closedBall z R)ᶜ B (gradient B) ∧
      Tendsto B (cocompact (Space n)) (𝓝 0) ∧
      ∀ a : Space n,dist a z=R → B a=
        (((p-(n : ℝ))/(p-1))*s^(-((p-(n : ℝ))/(p-1))))*
          fundamentalRadialValue n 1 p R := by
  let q : ℝ := (p-(n : ℝ))/(p-1)
  have hq : q<0 := div_neg_of_neg_of_pos (sub_neg.mpr hpn) (sub_pos.mpr hp)
  let C : ℝ := q*s^(-q)
  have hC : C<0 := mul_neg_of_neg_of_pos hq (Real.rpow_pos_of_pos hs _)
  let b : ContDiffBump (0 : Space n) :=
    ⟨s,(s+R)/2,hs,by linarith only [hsR]⟩
  have hbR : b.rOut<R := by dsimp only [b];linarith only [hsR]
  let B : Space n → ℝ := fun x => b (x-z)+C*flattenedRadialPrimitive n p b (x-z)
  have hflat := contDiff_flattenedRadialPrimitive n p b
  have hCinf : ContDiff ℝ ∞ B :=
    (b.contDiff.comp (contDiff_id.sub contDiff_const)).add
      (contDiff_const.mul (hflat.comp (contDiff_id.sub contDiff_const)))
  have hB_eq (x : Space n) (hx : b.rOut≤‖x-z‖) :
      B x=C*fundamentalPotential n 1 p (x-z) := by
    have hb : b (x-z)=0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
    simp only [B,flattenedRadialPrimitive,hb,sub_zero,one_mul,zero_add]
  have hbound (x : Space n) : B x≤1 := by
    by_cases hx : ‖x-z‖≤s
    · have hb : b (x-z)=1 := b.one_of_mem_closedBall
        (by simpa only [mem_closedBall,dist_zero_right] using hx)
      simp only [B,flattenedRadialPrimitive,hb,sub_self,zero_mul,mul_zero,add_zero,le_refl]
    · have hxs : s<‖x-z‖ := lt_of_not_ge hx
      have hm : fundamentalRadialValue n 1 p s≤fundamentalPotential n 1 p (x-z) := by
        rw [←fundamentalPotential_norm]
        exact (strictMonoOn_fundamentalRadialValue_all_p n zero_lt_one hp).monotoneOn
          hs (hs.trans hxs) hxs.le
      have hCF : C*fundamentalPotential n 1 p (x-z)≤1 := by
        have hh := mul_le_mul_of_nonpos_left hm hC.le
        exact hh.trans_eq (barrier_coefficient_normalizes hp hpn hs)
      have hh := mul_nonneg (sub_nonneg.mpr (b.le_one (x:=x-z))) (sub_nonneg.mpr hCF)
      change b (x-z)+C*((1-b (x-z))*fundamentalPotential n 1 p (x-z))≤1
      nlinarith only [hh]
  let O : Set (Space n) := (closedBall z R)ᶜ
  have hO : IsOpen O := isClosed_closedBall.isOpen_compl
  have hOx {x : Space n} (hx : x∈O) : b.rOut<‖x-z‖ := by
    have hh : R<dist x z := lt_of_not_ge hx
    exact hbR.trans (by simpa only [dist_eq_norm] using hh)
  have ht := ((weakPHarmonicPair_flattenedRadialPrimitive n hp b).smul C).source_zero.translate_actual (-z)
  have hu : WeakPHarmonicPair p {x : Space n | b.rOut<‖x-z‖}
      (fun x => C*flattenedRadialPrimitive n p b (x-z))
      (fun x => C • gradient (flattenedRadialPrimitive n p b) (x-z)) := by
    simpa only [Pi.smul_apply,smul_eq_mul,sub_eq_add_neg,preimage_setOf_eq] using ht.harmonic_of_source_zero
  have hEq : EqOn (fun x => C*flattenedRadialPrimitive n p b (x-z)) B O := by
    intro x hx
    have hb : b (x-z)=0 := b.zero_of_le_dist
      (by simpa only [dist_zero_right] using (hOx hx).le)
    simp only [B,hb,zero_add]
  have hweak : WeakPHarmonicPair p O B (gradient B) := by
    apply ((hu.mono (fun x hx => hOx hx) hO).congr_fun hEq).congr_gradient_on
    intro x hx
    have he : (fun y => C*flattenedRadialPrimitive n p b (y-z)) =ᶠ[𝓝 x] B := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact hEq hy
    calc
      C • gradient (flattenedRadialPrimitive n p b) (x-z)=
          gradient (fun y => C*flattenedRadialPrimitive n p b (y-z)) x := by
        rw [BMCompactCapacityV2.gradient_const_mul,barrier_gradient_sub hflat]
      _=gradient B x := he.gradient_eq
  have hnorm : Tendsto (fun x : Space n => ‖x-z‖) (cocompact (Space n)) atTop := by
    rw [←Metric.cobounded_eq_cocompact]
    simpa only [dist_eq_norm] using Metric.tendsto_dist_right_cobounded_atTop z
  have hpow : Tendsto (fun x : Space n => ‖x-z‖^q) (cocompact (Space n)) (𝓝 0) := by
    simpa only [neg_neg,Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hq)).comp hnorm
  have hF : Tendsto (fun x : Space n => fundamentalPotential n 1 p (x-z))
      (cocompact (Space n)) (𝓝 0) := by
    simpa only [fundamentalPotential,if_neg (ne_of_lt hpn),radialPowerPotential,
      Real.one_rpow,mul_one,mul_zero] using hpow.const_mul q⁻¹
  have hzero : Tendsto B (cocompact (Space n)) (𝓝 0) := by
    have hh := hF.const_mul C
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [hnorm.eventually (eventually_gt_atTop b.rOut)] with x hx
    exact (hB_eq x hx.le).symm
  refine ⟨B,hCinf,hbound,hweak,hzero,?_⟩
  intro a ha
  rw [hB_eq a (hbR.le.trans (by simpa only [dist_eq_norm] using ha.ge)),
    ←fundamentalPotential_norm,show ‖a-z‖=R by simpa only [dist_eq_norm] using ha]

/-- A genuine smooth lower-barrier sequence for an interior tangent ball.
All fields,harmonicity and both limiting conditions are constructed. -/
theorem exists_smooth_exterior_ball_barrier_sequence {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) (z : Space n) {R : ℝ} (hR : 0<R)
    {a : Space n} (ha : dist a z=R) :
    ∃ B : ℕ → Space n → ℝ,(∀ j,ContDiff ℝ ∞ (B j)) ∧ (∀ j x,B j x≤1) ∧
      (∀ j,WeakPHarmonicPair p (closedBall z R)ᶜ (B j) (gradient (B j))) ∧
      (∀ j,Tendsto (B j) (cocompact (Space n)) (𝓝 0)) ∧
      Tendsto (fun j => B j a) atTop (𝓝 1) := by
  classical
  let s : ℕ → ℝ := fun j => R*((j : ℝ)+1)/((j : ℝ)+2)
  have hs (j : ℕ) : 0<s j := div_pos (mul_pos hR (by positivity)) (by positivity)
  have hsR (j : ℕ) : s j<R := by
    dsimp only [s]
    apply (div_lt_iff₀ (by positivity : 0<(j : ℝ)+2)).mpr
    nlinarith only [hR]
  have hex (j : ℕ) := exists_smooth_fixed_ball_barrier hp hpn z (hs j) (hsR j)
  choose B hBc hB1 hBw hBzero hBa using hex
  refine ⟨B,hBc,hB1,hBw,hBzero,?_⟩
  have hinv : Tendsto (fun j : ℕ => ((j : ℝ)+2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hsLim : Tendsto s atTop (𝓝 R) := by
    have hh := ((tendsto_const_nhds (x:=(1 : ℝ))).sub hinv).const_mul R
    simp only [sub_zero,mul_one] at hh
    apply hh.congr'
    exact Eventually.of_forall (fun j => by
      dsimp only [s]
      field_simp
      <;> ring)
  let q : ℝ := (p-(n : ℝ))/(p-1)
  have hcoeff : Tendsto (fun j => (q*(s j)^(-q))*fundamentalRadialValue n 1 p R)
      atTop (𝓝 ((q*R^(-q))*fundamentalRadialValue n 1 p R)) :=
    (((Real.continuousAt_rpow_const R (-q) (Or.inl hR.ne')).tendsto.comp hsLim).const_mul q).mul_const _
  have hn := barrier_coefficient_normalizes hp hpn hR
  rw [hn] at hcoeff
  apply hcoeff.congr'
  exact Eventually.of_forall (fun j => (hBa j a ha).symm)

end BMCompactPDE
#print axioms BMCompactPDE.exists_smooth_exterior_ball_barrier_sequence
