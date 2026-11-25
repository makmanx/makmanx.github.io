import BMCompactCriticalChecked
import RegCaccioppoliInteger

/-! Genuine upper-level energy estimates for arbitrary weak subsolutions.
The positive-part cutoff tests are constructed from the distributional Sobolev
graph and actual W0 density. No continuity, classical regularity or test-
admissibility premise is supplied for the weak representative. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

/-- The ordinary truncated cutoff is an actual W0 test, with its actual weak
field, even when the input Sobolev representative is discontinuous. -/
theorem SobolevPair.upperCutoff_zeroBoundary
    {n M : ℕ} {p : ℝ} {D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p D u g) (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {η : Space n → ℝ} (hη : SmoothTest D η) (hη0 : ∀ x, 0≤η x)
    (hM : 2≤M) (k : ℝ) :
    ZeroBoundarySobolevPair p D
      (fun x => η x^M * max (u x-k) 0)
      (fun x => if k<u x then
        η x^M • g x + ((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x else 0) := by
  have hM0 : M≠0 := by omega
  have hMp : M-1≠0 := by omega
  have hz : SobolevPair p D (fun x => u x-k) g := by
    have hs := hu.add (sobolevPair_const hu.1 hDb (-k))
    exact hs.congr (Eventually.of_forall (fun x => by simp [sub_eq_add_neg]))
      (Eventually.of_forall (fun x => by simp))
  have hpow := hη.natPow_cutoff hM0
  have ht := hz.mul_smooth_compactSupport_zeroBoundary hD hpow.1 hpow.2.1 hpow.2.2
  have hd := hη.1.differentiable (by simp)
  have heG : (fun x => η x^M • g x+(u x-k) • gradient (fun y => η y^M) x) =
      (fun x => η x^M • g x+((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x) := by
    funext x
    rw [gradient_natPow_cutoff hd]
    simp only [smul_smul]
    congr 2
    ring
  rw [heG] at ht
  apply ht.positivePart.congr
  · exact Eventually.of_forall (fun x => by
      change max (η x^M*(u x-k)) 0 = η x^M*max (u x-k) 0
      by_cases hz : 0≤u x-k
      · rw [max_eq_left (mul_nonneg (pow_nonneg (hη0 x) M) hz),max_eq_left hz]
      · have hn := le_of_not_ge hz
        rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (hη0 x) M) hn),
          max_eq_right hn,mul_zero])
  · exact Eventually.of_forall (fun x => by
      change (if 0<η x^M*(u x-k) then η x^M • g x+((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x else 0) =
        (if k<u x then η x^M • g x+((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x else 0)
      by_cases hzero : η x=0
      · simp [hzero,zero_pow hM0,zero_pow hMp]
      · have hηpos : 0<η x := lt_of_le_of_ne (hη0 x) (Ne.symm hzero)
        have hpowpos : 0<η x^M := pow_pos hηpos M
        have he : 0<η x^M*(u x-k) ↔ k<u x := by
          rw [mul_pos_iff_of_pos_left hpowpos,sub_pos]
        simp only [he])

/-- Actual upper-level Caccioppoli for weak p-subsolutions. Unlike the earlier
untruncated harmonic estimate, the energy is restricted to {u>k}. -/
theorem WeakPSubsolutionPair.caccioppoli_upper_natPow
    {n M : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1)
    (hm : p≤(M : ℝ)) (k : ℝ) :
    (∫ x in D, if k<u x then η x^M*‖g x‖^p else 0) ≤
      (M : ℝ)^p * ∫ x in D, (max (u x-k) 0)^p * ‖gradient η x‖^p := by
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hMreal : (1 : ℝ)<(M : ℝ) := hu.1.trans_le hm
  have hM2 : 2≤M := by exact_mod_cast hMreal
  have hM0 : M≠0 := by omega
  have hM1 : 1≤M := by omega
  have hcast : ((M-1 : ℕ) : ℝ)=(M : ℝ)-1 := by
    rw [Nat.cast_sub hM1]
    norm_num
  let μ := volume.restrict D
  let A : Space n → ℝ := fun x => if k<u x then η x^M*‖g x‖^p else 0
  let B : Space n → ℝ := fun x => (max (u x-k) 0)^p*‖gradient η x‖^p
  let C : Space n → ℝ := fun x =>
    (M : ℝ)*η x^(M-1)*max (u x-k) 0 * inner ℝ (pFlux p (g x)) (gradient η x)
  let W : Space n → Space n := fun x => if k<u x then
    η x^M • g x+((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x else 0
  have hS := hu.2.2.1 D hD
  have hg := hS.2.2.1
  have hGI := integrable_norm_rpow_of_memLp hu.1 hg
  have hbaseI : Integrable (fun x => η x^M*‖g x‖^p) μ := by
    apply hGI.mono_nonneg ((hη.1.continuous.pow M).aestronglyMeasurable.mul hGI.1)
    · exact Eventually.of_forall (fun x => mul_nonneg
        (pow_nonneg (hη0 x) M) (Real.rpow_nonneg (norm_nonneg _) _))
    · exact Eventually.of_forall (fun x => by
        have he : η x^M≤1 := by
          simpa only [Real.rpow_natCast] using
            Real.rpow_le_one (hη0 x) (hη1 x) (show 0≤(M : ℝ) by positivity)
        exact (mul_le_mul_of_nonneg_right he
          (Real.rpow_nonneg (norm_nonneg (g x)) p)).trans_eq (one_mul _))
  have hAI : Integrable A μ := by
    change Integrable ({x | k<u x}.indicator (fun x => η x^M*‖g x‖^p)) μ
    exact hbaseI.indicator₀ (nullMeasurableSet_lt aemeasurable_const hS.2.1.1.aemeasurable)
  have hz : MemLp (fun x => u x-k) (ENNReal.ofReal p) μ := by
    have hs := hS.add (sobolevPair_const hu.1 hD.2.1 (-k))
    have hs' : SobolevPair p D (fun x => u x-k) g := hs.congr (Eventually.of_forall (fun x => by simp [sub_eq_add_neg]))
      (Eventually.of_forall (fun x => by simp))
    exact hs'.2.1
  have hzm : MemLp (fun x => max (u x-k) 0) (ENNReal.ofReal p) μ := by
    apply hz.of_le ((continuous_id.max continuous_const).comp_aestronglyMeasurable hz.1)
    exact Eventually.of_forall (fun x => by
      change ‖max (u x-k) 0‖≤‖u x-k‖
      by_cases hx : u x-k≤0
      · simp only [max_eq_right hx,norm_zero]
        exact norm_nonneg _
      · rw [max_eq_left (lt_of_not_ge hx).le])
  have hzI : Integrable (fun x => (max (u x-k) 0)^p) μ := by
    have hi := hzm.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
    have he : (fun x => ‖max (u x-k) 0‖^(ENNReal.ofReal p).toReal) =
        (fun x => (max (u x-k) 0)^p) := by
      funext x
      rw [ENNReal.toReal_ofReal hp0.le,Real.norm_eq_abs,abs_of_nonneg (le_max_right (u x-k) 0)]
    rw [he] at hi
    exact hi
  have hgrad : Continuous (gradient η) :=
    BMCompactCapacityV2.continuous_gradient_of_contDiff hη.1
  obtain ⟨c,hc⟩ := (BMCompactCapacityV2.gradient_hasCompactSupport hη.2.1).exists_bound_of_continuous hgrad
  let c' : ℝ := max c 0
  have hc0 : 0≤c' := le_max_right _ _
  have hcb (x : Space n) : ‖gradient η x‖≤c' := (hc x).trans (le_max_left _ _)
  have hgradp : Continuous (fun x => ‖gradient η x‖^p) :=
    hgrad.norm.rpow_const (fun _ => Or.inr hp0.le)
  have hBI : Integrable B μ := by
    apply (hzI.mul_const (c'^p)).mono_nonneg (hzI.1.mul hgradp.aestronglyMeasurable)
    · exact Eventually.of_forall (fun x => mul_nonneg
        (Real.rpow_nonneg (le_max_right _ _) _) (Real.rpow_nonneg (norm_nonneg _) _))
    · exact Eventually.of_forall (fun x => mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (hcb x) hp0.le)
        (Real.rpow_nonneg (le_max_right _ _) _))
  have ht := hS.upperCutoff_zeroBoundary hD.1 hD.2.1 hη hη0 hM2 k
  obtain ⟨hFI,hFle⟩ := hu.2.2.2 D hD _ W ht
    (Eventually.of_forall (fun x => mul_nonneg (pow_nonneg (hη0 x) M) (le_max_right _ _)))
  have hdecomp : fluxPairing p g W=A+C := by
    funext x
    by_cases hx : k<u x
    · simp only [fluxPairing,W,A,C,if_pos hx,Pi.add_apply,inner_add_right,
        inner_smul_right,pFlux_inner_self hu.1,max_eq_left (sub_pos.mpr hx).le]
    · have hz : u x-k≤0 := sub_nonpos.mpr (le_of_not_gt hx)
      simp [fluxPairing,W,A,C,hx,max_eq_right hz]
  have hCI : Integrable C μ := by
    have hh := hFI.sub hAI
    simpa only [hdecomp,Pi.sub_apply,Pi.add_apply,add_sub_cancel_left] using! hh
  rw [hdecomp] at hFle
  simp only [Pi.add_apply] at hFle
  rw [integral_add hAI hCI] at hFle
  have habs (x : Space n) : -C x ≤ ((p-1)/p)*A x+((M : ℝ)^p/p)*B x := by
    by_cases hx : k<u x
    · have h := cutoff_flux_cross_absorption hu.1 hm (hη0 x) (hη1 x)
        (g x) (gradient η x) (z := u x-k)
      rw [←hcast,Real.rpow_natCast,Real.rpow_natCast] at h
      simpa only [C,A,B,if_pos hx,max_eq_left (sub_pos.mpr hx).le,abs_of_pos (sub_pos.mpr hx)] using h
    · have hz : u x-k≤0 := sub_nonpos.mpr (le_of_not_gt hx)
      simp [C,A,B,hx,max_eq_right hz,Real.zero_rpow hp0.ne']
  have hb := integral_mono hCI.neg
    ((hAI.const_mul ((p-1)/p)).add (hBI.const_mul ((M : ℝ)^p/p))) habs
  simp only [Pi.neg_apply,Pi.add_apply] at hb
  rw [integral_neg,integral_add (hAI.const_mul ((p-1)/p))
    (hBI.const_mul ((M : ℝ)^p/p)),integral_const_mul,integral_const_mul] at hb
  have hmul := mul_le_mul_of_nonneg_left hb hp0.le
  have hα : p*((p-1)/p)=p-1 := by field_simp
  have hβ : p*((M : ℝ)^p/p)=(M : ℝ)^p := by field_simp
  rw [mul_add,←mul_assoc,hα,←mul_assoc,hβ] at hmul
  change (∫ x, A x ∂μ)≤(M : ℝ)^p*∫ x, B x ∂μ
  have hscaled := mul_nonpos_of_nonneg_of_nonpos hp0.le hFle
  nlinarith

theorem WeakPHarmonicPair.caccioppoli_upper_natPow
    {n M : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1)
    (hm : p≤(M : ℝ)) (k : ℝ) :
    (∫ x in D, if k<u x then η x^M*‖g x‖^p else 0) ≤
      (M : ℝ)^p * ∫ x in D, (max (u x-k) 0)^p * ‖gradient η x‖^p :=
  hu.subsolution.caccioppoli_upper_natPow hD hη hη0 hη1 hm k

end BMCompactPDE
#print axioms BMCompactPDE.SobolevPair.upperCutoff_zeroBoundary
#print axioms BMCompactPDE.WeakPSubsolutionPair.caccioppoli_upper_natPow
#print axioms BMCompactPDE.WeakPHarmonicPair.caccioppoli_upper_natPow
