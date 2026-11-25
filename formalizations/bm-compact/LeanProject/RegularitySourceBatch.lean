import PotentialTruncatedEnergy
import ContactForcedComparison
import NonlinearAnalyticBatch

/-! Prospective source-only batch of four constant-source regularity statements.
Prepared only; no native verdict or proof count is inferred from this export. -/

/- Body retained from RegularitySourceCaccioppoli.lean; see the adjacent exact provenance map. -/
noncomputable section RegularityBody_RegularitySourceCaccioppoli

/-! DEVELOPMENT DRAFT: actual source Caccioppoli through the genuine full-W0
positive cutoff test. The source term is retained explicitly; no zero-source
subsolution property, a priori upper bound or classical regularity of u is
supplied. This extends the checked zero-source absorption argument. It is not
part of any native/proof count until an explicit successful check. -/
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

theorem WeakPSourceSubsolutionPair.caccioppoli_upper_natPow_source
    {n M : ℕ} {p c : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1)
    (hm : p≤(M : ℝ)) (k : ℝ) :
    (∫ x in D, if k<u x then η x^M*‖g x‖^p else 0) ≤
      (M : ℝ)^p * (∫ x in D, (max (u x-k) 0)^p * ‖gradient η x‖^p) +
        p*c*(∫ x in D, η x^M*max (u x-k) 0) := by
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
  obtain ⟨cutoffBound,hcutoffBound⟩ :=
    (BMCompactCapacityV2.gradient_hasCompactSupport hη.2.1).exists_bound_of_continuous hgrad
  let c' : ℝ := max cutoffBound 0
  have hc0 : 0≤c' := le_max_right _ _
  have hcb (x : Space n) : ‖gradient η x‖≤c' := (hcutoffBound x).trans (le_max_left _ _)
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
  change (∫ x, A x ∂μ)≤(M : ℝ)^p*(∫ x, B x ∂μ)+
    p*c*(∫ x, η x^M*max (u x-k) 0 ∂μ)
  have hscaled := mul_le_mul_of_nonneg_left hFle hp0.le
  nlinarith only [hscaled,hmul]

end BMCompactPDE

end RegularityBody_RegularitySourceCaccioppoli

/- Body retained from RegularitySourceBounded.lean; see the adjacent exact provenance map. -/
noncomputable section RegularityBody_RegularitySourceBounded

/-! UNCOMPILED source-regularity development. The actual constant forcing term
is kept through full-W0 Caccioppoli and midpoint truncations. No upper bound or
classical regularity of the weak function is supplied. This draft adds zero
proof counts until a successful check after the zero-source boundedness batch. -/
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

private def regularitySourceLevelEnergy {n : ℕ} (p : ℝ) (M : ℕ) (η u : Space n → ℝ)
    (g : Space n → Space n) (k : ℝ) : Space n → ℝ :=
  fun x => if k<u x then η x^M*‖g x‖^p else 0

private def regularitySourceLevelMoment {n : ℕ} (p : ℝ) (η u : Space n → ℝ) (k : ℝ) : Space n → ℝ :=
  fun x => (max (u x-k) 0)^p*‖gradient η x‖^p

private def regularitySourceCutoffField {n : ℕ} (M : ℕ) (η u : Space n → ℝ)
    (g : Space n → Space n) (k : ℝ) : Space n → Space n :=
  fun x => if k<u x then
    η x^M • g x+((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x else 0

private theorem regularity_source_norm_add_rpow_le {n : ℕ} {p : ℝ} (hp : 0≤p)
    (a b : Space n) :
    ‖a+b‖^p ≤ (2 : ℝ)^p*(‖a‖^p+‖b‖^p) := by
  by_cases hab : ‖a‖≤‖b‖
  · have hn : ‖a+b‖≤2*‖b‖ := (norm_add_le a b).trans (by linarith)
    have hr := Real.rpow_le_rpow (norm_nonneg _) hn hp
    rw [Real.mul_rpow (by norm_num) (norm_nonneg b)] at hr
    exact hr.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg a) p))
      (Real.rpow_nonneg (by norm_num) p))
  · have hn : ‖a+b‖≤2*‖a‖ := (norm_add_le a b).trans (by linarith)
    have hr := Real.rpow_le_rpow (norm_nonneg _) hn hp
    rw [Real.mul_rpow (by norm_num) (norm_nonneg a)] at hr
    exact hr.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg b) p))
      (Real.rpow_nonneg (by norm_num) p))

private theorem regularity_source_cutoff_energy_pointwise {n M : ℕ} {p : ℝ}
    (hp : 1<p) {η u : Space n → ℝ} {g : Space n → Space n}
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1) (k : ℝ) (x : Space n) :
    ‖regularitySourceCutoffField M η u g k x‖^p ≤
      (2 : ℝ)^p*(regularitySourceLevelEnergy p M η u g k x+
        (M : ℝ)^p*regularitySourceLevelMoment p η u k x) := by
  have hp0 : 0<p := zero_lt_one.trans hp
  by_cases hx : k<u x
  · have hz : 0<u x-k := sub_pos.mpr hx
    have hM0 : 0≤(M : ℝ) := by positivity
    have hηM : 0≤η x^M := pow_nonneg (hη0 x) M
    have hηM1 : η x^M≤1 := pow_le_one₀ (hη0 x) (hη1 x)
    have hηP : 0≤η x^(M-1) := pow_nonneg (hη0 x) _
    have hηP1 : η x^(M-1)≤1 := pow_le_one₀ (hη0 x) (hη1 x)
    have hA : ‖η x^M • g x‖^p ≤ η x^M*‖g x‖^p := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hηM,
        Real.mul_rpow hηM (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_le_one hηM hηM1 hp.le)
        (Real.rpow_nonneg (norm_nonneg _) _)
    have hcoef0 : 0≤(M : ℝ)*η x^(M-1)*(u x-k) :=
      mul_nonneg (mul_nonneg hM0 hηP) hz.le
    have hcoef : (M : ℝ)*η x^(M-1)*(u x-k) ≤ (M : ℝ)*(u x-k) := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hηP1 hM0) hz.le
      simpa only [mul_one] using h
    have hn : ‖((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x‖ ≤
        ((M : ℝ)*(u x-k))*‖gradient η x‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hcoef0]
      exact mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    have hB := Real.rpow_le_rpow (norm_nonneg _) hn hp0.le
    rw [Real.mul_rpow (mul_nonneg hM0 hz.le) (norm_nonneg _),
      Real.mul_rpow hM0 hz.le] at hB
    have hh := regularity_source_norm_add_rpow_le hp0.le
      (η x^M • g x) (((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x)
    simp only [regularitySourceCutoffField,regularitySourceLevelEnergy,regularitySourceLevelMoment,
      if_pos hx,max_eq_left hz.le]
    exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add hA (by
      simpa only [mul_assoc] using hB)) (Real.rpow_nonneg (by norm_num) p))
  · have hz : u x-k≤0 := sub_nonpos.mpr (le_of_not_gt hx)
    simp [regularitySourceCutoffField,regularitySourceLevelEnergy,regularitySourceLevelMoment,hx,
      max_eq_right hz,Real.zero_rpow hp0.ne']

private theorem regularity_source_level_energy_integrable {n M : ℕ} {p : ℝ}
    {D : Set (Space n)} {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p D u g) (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1) (k : ℝ) :
    Integrable (regularitySourceLevelEnergy p M η u g k) (volume.restrict D) := by
  have hGI := integrable_norm_rpow_of_memLp hu.1 hu.2.2.1
  have hi : Integrable (fun x => η x^M*‖g x‖^p) (volume.restrict D) := by
    apply hGI.mono_nonneg ((hη.1.continuous.pow M).aestronglyMeasurable.mul hGI.1)
    · exact Eventually.of_forall (fun x => mul_nonneg
        (pow_nonneg (hη0 x) M) (Real.rpow_nonneg (norm_nonneg _) _))
    · exact Eventually.of_forall (fun x =>
        (mul_le_mul_of_nonneg_right (pow_le_one₀ (hη0 x) (hη1 x))
          (Real.rpow_nonneg (norm_nonneg (g x)) p)).trans_eq (one_mul _))
  exact hi.indicator₀ (nullMeasurableSet_lt aemeasurable_const hu.2.1.1.aemeasurable)

private theorem regularity_source_level_moment_integrable {n : ℕ} {p : ℝ}
    {D : Set (Space n)} {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p D u g) (hDb : Bornology.IsBounded D)
    (hη : SmoothTest D η) (k : ℝ) :
    Integrable (regularitySourceLevelMoment p η u k) (volume.restrict D) := by
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hz : SobolevPair p D (fun x => u x-k) g := by
    exact (hu.add (sobolevPair_const hu.1 hDb (-k))).congr
      (Eventually.of_forall (fun x => by simp [sub_eq_add_neg]))
      (Eventually.of_forall (fun x => by simp))
  have hm := hz.2.1.pos_part
  have hgradtop : MemLp (gradient η) (∞ : ℝ≥0∞) (volume.restrict D) :=
    (BMCompactCapacityV2.continuous_gradient_of_contDiff hη.1).memLp_top_of_hasCompactSupport
      (BMCompactCapacityV2.gradient_hasCompactSupport hη.2.1) _
  have hY : MemLp (fun x => max (u x-k) 0 • gradient η x)
      (ENNReal.ofReal p) (volume.restrict D) := hgradtop.smul hm
  have hi := integrable_norm_rpow_of_memLp hu.1 hY
  have he : (fun x => ‖max (u x-k) 0 • gradient η x‖^p)=
      regularitySourceLevelMoment p η u k := by
    funext x
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (le_max_right (u x-k) 0),
      Real.mul_rpow (le_max_right _ _) (norm_nonneg _)]
    rfl
  rw [he] at hi
  exact hi

private theorem regularity_source_cutoff_gradient_energy
    {n M : ℕ} {p c : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1)
    (hm : p≤(M : ℝ)) (k : ℝ) :
    (∫ x in D, ‖if k<u x then
        η x^M • g x+((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x else 0‖^p) ≤
      ((2 : ℝ)^p*(2*(M : ℝ)^p)) *
        (∫ x in D, (max (u x-k) 0)^p*‖gradient η x‖^p) +
      ((2 : ℝ)^p*p)*c*(∫ x in D, η x^M*max (u x-k) 0) := by
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hM2 : 2≤M := by exact_mod_cast hu.1.trans_le hm
  have hs := hu.2.2.1 D hD
  have hw := hs.upperCutoff_zeroBoundary hD.1 hD.2.1 hη hη0 hM2 k
  let A := regularitySourceLevelEnergy p M η u g k
  let B := regularitySourceLevelMoment p η u k
  let W := regularitySourceCutoffField M η u g k
  have hAI : Integrable A (volume.restrict D) := regularity_source_level_energy_integrable hs hη hη0 hη1 k
  have hBI : Integrable B (volume.restrict D) := regularity_source_level_moment_integrable hs hD.2.1 hη k
  have hWI : Integrable (fun x => ‖W x‖^p) (volume.restrict D) :=
    integrable_norm_rpow_of_memLp hu.1 hw.1.2.2.1
  have hi := integral_mono hWI
    ((hAI.add (hBI.const_mul ((M : ℝ)^p))).const_mul ((2 : ℝ)^p))
    (fun x => regularity_source_cutoff_energy_pointwise hu.1 hη0 hη1 k x)
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add hAI (hBI.const_mul ((M : ℝ)^p)),
    integral_const_mul] at hi
  have hc := hu.caccioppoli_upper_natPow_source hD hη hη0 hη1 hm k
  change (∫ x in D, A x) ≤ (M : ℝ)^p*(∫ x in D, B x)+
    p*c*(∫ x in D, η x^M*max (u x-k) 0) at hc
  have hh := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (by norm_num : (0 : ℝ)≤2) p)
  change (∫ x in D, ‖W x‖^p) ≤ ((2 : ℝ)^p*(2*(M : ℝ)^p))*(∫ x in D, B x)+
    ((2 : ℝ)^p*p)*c*(∫ x in D, η x^M*max (u x-k) 0)
  nlinarith only [hi,hh]

/-- The midpoint source moment is controlled by the preceding weighted tail.
Only scalar level/cutoff data occur here; there is no bound on u. -/
private theorem regularity_source_moment_pointwise {p e a l m : ℝ} (s N : ℕ)
    (hp : 1<p) (he0 : 0≤e) (he1 : e≤1) (hlm : l<m)
    (hNs : (s : ℝ)*p≤(N : ℝ)) :
    e^N*max (a-m) 0 ≤ (m-l)^(1-p)*(e^s*max (a-l) 0)^p := by
  have hp0 : 0<p := zero_lt_one.trans hp
  have hδ : 0<m-l := sub_pos.mpr hlm
  by_cases ham : m<a
  · have hal : 0<a-l := by linarith
    have ham0 : 0≤a-m := (sub_pos.mpr ham).le
    have hδa : m-l≤a-l := by linarith
    have hpow : e^N≤(e^s)^p := by
      calc
        e^N=e^(N : ℝ) := by rw [Real.rpow_natCast]
        _ ≤ e^((s : ℝ)*p) := Real.rpow_le_rpow_of_exponent_ge' he0 he1
          (mul_nonneg (Nat.cast_nonneg _) hp0.le) hNs
        _ = (e^s)^p := by rw [Real.rpow_mul he0,Real.rpow_natCast]
    have hlev : a-l≤(m-l)^(1-p)*(a-l)^p := by
      have hh := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hδ hδa (by linarith : 1-p≤0))
        (Real.rpow_nonneg hal.le p)
      have heq : (a-l)^(1-p)*(a-l)^p=a-l := by
        rw [←Real.rpow_add hal]
        have hsum : 1-p+p=1 := by ring
        rw [hsum,Real.rpow_one]
      rw [heq] at hh
      exact hh
    rw [max_eq_left ham0,max_eq_left hal.le]
    calc
      e^N*(a-m) ≤ e^N*(a-l) :=
        mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg he0 N)
      _ ≤ (e^s)^p*(a-l) := mul_le_mul_of_nonneg_right hpow hal.le
      _ ≤ (e^s)^p*((m-l)^(1-p)*(a-l)^p) :=
        mul_le_mul_of_nonneg_left hlev (Real.rpow_nonneg (pow_nonneg he0 s) p)
      _ = (m-l)^(1-p)*(e^s*(a-l))^p := by
        rw [Real.mul_rpow (pow_nonneg he0 s) hal.le]
        ring
  · rw [max_eq_right (by linarith : a-m≤0),mul_zero]
    exact mul_nonneg (Real.rpow_nonneg hδ.le _)
      (Real.rpow_nonneg (mul_nonneg (pow_nonneg he0 s) (le_max_right _ _)) _)

private theorem regularity_source_delta_power {p K b : ℝ} (j : ℕ)
    (hp : 1<p) (hK1 : 1≤K) (hb2 : (2 : ℝ)≤b) :
    (K*(1/2 : ℝ)^(j+2))^(1-p) ≤ (4 : ℝ)^p*(b^j)^p := by
  have hK : 0<K := zero_lt_one.trans_le hK1
  have hb : 0<b := by linarith
  have hδ : 0<K*(1/2 : ℝ)^(j+2) := by positivity
  have hKi : K⁻¹≤1 := by
    rw [←one_div]
    exact (div_le_iff₀ hK).mpr (by simpa using hK1)
  have htwo : (2 : ℝ)^j≤b^j := pow_le_pow_left₀ (by norm_num) hb2 j
  have hr1 : (1 : ℝ)≤b^j := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1)
      (show (1 : ℝ)≤b by linarith) j
  have hinv : (((1/2 : ℝ)^(j+2)))⁻¹=(2 : ℝ)^(j+2) := by
    rw [←inv_pow]
    norm_num
  have hδinv : (K*(1/2 : ℝ)^(j+2))⁻¹≤4*b^j := by
    rw [mul_inv_rev,hinv]
    calc
      (2 : ℝ)^(j+2)*K⁻¹=(4*(2 : ℝ)^j)*K⁻¹ := by
        rw [pow_add,show (2 : ℝ)^2=4 by norm_num]
        ring
      _ ≤ 4*(2 : ℝ)^j :=
        (mul_le_mul_of_nonneg_left hKi (by positivity)).trans_eq (mul_one _)
      _ ≤ 4*b^j := mul_le_mul_of_nonneg_left htwo (by norm_num)
  have he : (K*(1/2 : ℝ)^(j+2))^(1-p)=
      ((K*(1/2 : ℝ)^(j+2))⁻¹)^(p-1) := by
    have hpower : 1-p=(-1 : ℝ)*(p-1) := by ring
    rw [hpower,Real.rpow_mul hδ.le,Real.rpow_neg_one]
  rw [he]
  calc
    ((K*(1/2 : ℝ)^(j+2))⁻¹)^(p-1) ≤ (4*b^j)^(p-1) :=
      Real.rpow_le_rpow (inv_nonneg.mpr hδ.le) hδinv (sub_nonneg.mpr hp.le)
    _ ≤ (4*b^j)^p := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (4 : ℝ)^p*(b^j)^p := Real.mul_rpow (by norm_num) (pow_nonneg hb.le j)

private theorem regularity_source_weighted_memLp {n : ℕ} {p : ℝ}
    {D : Set (Space n)} {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p D u g) (hDb : Bornology.IsBounded D)
    (hη : Continuous η) (hη0 : ∀ x,0≤η x) (hη1 : ∀ x,η x≤1)
    (s : ℕ) (k : ℝ) :
    MemLp (fun x => η x^s*max (u x-k) 0) (ENNReal.ofReal p) (volume.restrict D) := by
  have hz : SobolevPair p D (fun x => u x-k) g := by
    exact (hu.add (sobolevPair_const hu.1 hDb (-k))).congr
      (Eventually.of_forall (fun x => by simp [sub_eq_add_neg]))
      (Eventually.of_forall (fun x => by simp))
  have hm := hz.2.1.pos_part
  have htop : MemLp (fun x => η x^s) ∞ (volume.restrict D) :=
    memLp_top_of_bound (hη.pow s).aestronglyMeasurable 1
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hη0 x) s)]
        exact pow_le_one₀ (hη0 x) (hη1 x)))
  exact hm.mul' htop

private theorem regularity_source_midpoint_sobolev
    {n M r : ℕ} {p c G l m : ℝ} {Ω D : Set (Space n)}
    {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (hD : LocalDomain D Ω)
    (hη : SmoothTest D η) (hη0 : ∀ x,0≤η x) (hη1 : ∀ x,η x≤1)
    (hc : 0≤c) (hG : 0≤G) (hgrad : ∀ x∈D,‖gradient η x‖≤G)
    (hr : 0<r) (hm : p≤(M : ℝ)) (hpn : p<(n : ℝ)) (hlm : l<m)
    (hδpower : (m-l)^(1-p)≤(4 : ℝ)^p*(r : ℝ)^p) :
    eLpNorm' (fun x => η x^(M*r)*max (u x-m) 0)
      ((n : ℝ)*p/((n : ℝ)-p)) (volume.restrict D) ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p : ℝ≥0∞) *
        ENNReal.ofReal ((((2 : ℝ)^p*(2*(M : ℝ)^p))*G^p+
          ((2 : ℝ)^p*p)*c*(4 : ℝ)^p)^p⁻¹) * ENNReal.ofReal (r : ℝ) *
        eLpNorm' (fun x => η x^(r-1)*max (u x-l) 0) p (volume.restrict D) := by
  let μ := volume.restrict D
  let ψ : Space n → ℝ := fun x => η x^r
  let wl : Space n → ℝ := fun x => max (u x-l) 0
  let wm : Space n → ℝ := fun x => max (u x-m) 0
  let Z : Space n → ℝ := fun x => η x^(r-1)*wl x
  let Φ : Space n → ℝ := fun x => ψ x^M*wm x
  let W : Space n → Space n := regularitySourceCutoffField M ψ u g m
  let B : Space n → ℝ := regularitySourceLevelMoment p ψ u m
  let E : ℝ := (2 : ℝ)^p*(2*(M : ℝ)^p)
  let F : ℝ := (2 : ℝ)^p*p
  let H : ℝ := E*G^p+F*c*(4 : ℝ)^p
  let Q : ℝ := (n : ℝ)*p/((n : ℝ)-p)
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hn0 : 0<(n : ℝ) := hp0.trans hpn
  have hQ : 0<Q := div_pos (mul_pos hn0 hp0) (sub_pos.mpr hpn)
  have hP0 : ENNReal.ofReal p≠0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hQ0 : ENNReal.ofReal Q≠0 := ENNReal.ofReal_ne_zero_iff.mpr hQ
  have hM2 : 2≤M := by exact_mod_cast hu.1.trans_le hm
  have hψ : SmoothTest D ψ := hη.natPow_cutoff hr.ne'
  have hψ0 (x : Space n) : 0≤ψ x := pow_nonneg (hη0 x) r
  have hψ1 (x : Space n) : ψ x≤1 := pow_le_one₀ (hη0 x) (hη1 x)
  have hs := hu.2.2.1 D hD
  have hθ : ZeroBoundarySobolevPair p D Φ W :=
    hs.upperCutoff_zeroBoundary hD.1 hD.2.1 hψ hψ0 hM2 m
  have hW : MemLp W (ENNReal.ofReal p) μ := hθ.1.2.2.1
  have hZ : MemLp Z (ENNReal.ofReal p) μ :=
    regularity_source_weighted_memLp hs hD.2.1 hη.1.continuous hη0 hη1 (r-1) l
  have hZI : Integrable (fun x => ‖Z x‖^p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      hZ.integrable_norm_rpow hP0 ENNReal.ofReal_ne_top
  have hBI : Integrable B μ := regularity_source_level_moment_integrable hs hD.2.1 hψ m
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hD.2.1.measure_lt_top.ne
  have hΦI : Integrable Φ μ := MemLp.integrable (ENNReal.one_le_ofReal.mpr hu.1.le) hθ.1.2.1
  have hZ0 (x : Space n) : 0≤Z x :=
    mul_nonneg (pow_nonneg (hη0 x) _) (le_max_right _ _)
  have hr0 : 0≤(r : ℝ) := Nat.cast_nonneg _
  have hrG : 0≤(r : ℝ)*G := mul_nonneg hr0 hG
  have hBpoint : B≤ᵐ[μ] fun x => ((r : ℝ)*G)^p*‖Z x‖^p := by
    filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hxD
    have hwl : 0≤wl x := le_max_right _ _
    have hwm : 0≤wm x := le_max_right _ _
    have hml : wm x≤wl x := max_le_max (sub_le_sub_left hlm.le _) le_rfl
    have hd : gradient ψ x=((r : ℝ)*η x^(r-1)) • gradient η x :=
      gradient_natPow_cutoff (hη.1.differentiable (by simp)) r x
    have hcoef : 0≤(r : ℝ)*η x^(r-1) := mul_nonneg hr0 (pow_nonneg (hη0 x) _)
    have hgradψ : ‖gradient ψ x‖≤((r : ℝ)*G)*η x^(r-1) := by
      rw [hd,norm_smul,Real.norm_eq_abs,abs_of_nonneg hcoef]
      nlinarith only [mul_le_mul_of_nonneg_left (hgrad x hxD) hcoef]
    have hprod : wm x*‖gradient ψ x‖≤((r : ℝ)*G)*Z x := by
      calc
        wm x*‖gradient ψ x‖ ≤ wl x*‖gradient ψ x‖ :=
          mul_le_mul_of_nonneg_right hml (norm_nonneg _)
        _ ≤ wl x*(((r : ℝ)*G)*η x^(r-1)) := mul_le_mul_of_nonneg_left hgradψ hwl
        _ = ((r : ℝ)*G)*Z x := by dsimp only [Z];ring
    have hpw := Real.rpow_le_rpow (mul_nonneg hwm (norm_nonneg _)) hprod hp0.le
    rw [Real.mul_rpow hwm (norm_nonneg _),Real.mul_rpow hrG (hZ0 x)] at hpw
    change wm x^p*‖gradient ψ x‖^p≤((r : ℝ)*G)^p*‖Z x‖^p
    rw [Real.norm_eq_abs,abs_of_nonneg (hZ0 x)]
    exact hpw
  have hBbound := integral_mono_ae hBI (hZI.const_mul (((r : ℝ)*G)^p)) hBpoint
  rw [integral_const_mul,Real.mul_rpow hr0 hG] at hBbound
  have hr1 : 1≤r := Nat.succ_le_iff.mpr hr
  have hNs : ((r-1 : ℕ) : ℝ)*p≤((M*r : ℕ) : ℝ) := by
    rw [Nat.cast_sub hr1,Nat.cast_one,Nat.cast_mul]
    nlinarith only [mul_le_mul_of_nonneg_right hm hr0,hp0]
  have hΦpoint (x : Space n) : Φ x≤(m-l)^(1-p)*‖Z x‖^p := by
    have hh := regularity_source_moment_pointwise (r-1) (M*r) hu.1
      (hη0 x) (hη1 x) hlm hNs (a := u x)
    change ψ x^M*wm x≤(m-l)^(1-p)*‖Z x‖^p
    rw [Real.norm_eq_abs,abs_of_nonneg (hZ0 x)]
    simpa only [ψ,wm,Z,wl,←pow_mul,Nat.mul_comm] using hh
  have hTbound := integral_mono hΦI (hZI.const_mul ((m-l)^(1-p))) hΦpoint
  rw [integral_const_mul] at hTbound
  have hI0 : 0≤∫ x,‖Z x‖^p ∂μ := integral_nonneg
    (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have hT' := hTbound.trans (mul_le_mul_of_nonneg_right hδpower hI0)
  have hE : 0≤E := by dsimp only [E];positivity
  have hF : 0≤F := by dsimp only [F];positivity
  have hH : 0≤H := add_nonneg (mul_nonneg hE (Real.rpow_nonneg hG p))
    (mul_nonneg (mul_nonneg hF hc) (Real.rpow_nonneg (by norm_num) p))
  have henergy := regularity_source_cutoff_gradient_energy hu hD hψ hψ0 hψ1 hm m
  change (∫ x,‖W x‖^p ∂μ)≤E*(∫ x,B x ∂μ)+F*c*(∫ x,Φ x ∂μ) at henergy
  have hEB := mul_le_mul_of_nonneg_left hBbound hE
  have hFT := mul_le_mul_of_nonneg_left hT' (mul_nonneg hF hc)
  have hfield : (∫ x,‖W x‖^p ∂μ)≤H*(r : ℝ)^p*(∫ x,‖Z x‖^p ∂μ) := by
    dsimp only [H]
    nlinarith only [henergy,hEB,hFT]
  have hWeq := hW.eLpNorm_eq_integral_rpow_norm hP0 ENNReal.ofReal_ne_top
  have hZeq := hZ.eLpNorm_eq_integral_rpow_norm hP0 ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal hp0.le] at hWeq hZeq
  have hnorm : eLpNorm W (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (H^p⁻¹)*ENNReal.ofReal (r : ℝ)*eLpNorm Z (ENNReal.ofReal p) μ := by
    calc
      eLpNorm W (ENNReal.ofReal p) μ=ENNReal.ofReal ((∫ x,‖W x‖^p ∂μ)^p⁻¹) := hWeq
      _ ≤ ENNReal.ofReal ((H*(r : ℝ)^p*(∫ x,‖Z x‖^p ∂μ))^p⁻¹) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
          (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hfield
          (inv_nonneg.mpr hp0.le))
      _ = ENNReal.ofReal (H^p⁻¹)*ENNReal.ofReal (r : ℝ)*eLpNorm Z (ENNReal.ofReal p) μ := by
        rw [Real.mul_rpow (mul_nonneg hH (Real.rpow_nonneg hr0 p)) hI0,
          Real.mul_rpow hH (Real.rpow_nonneg hr0 p),Real.rpow_rpow_inv hr0 hp0.ne',
          ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hH _) hr0),
          ENNReal.ofReal_mul (Real.rpow_nonneg hH _),←hZeq]
  have hb := (hθ.critical_sobolev_explicit hpn).2.trans
    (mul_le_mul_of_nonneg_left hnorm bot_le)
  rw [eLpNorm_eq_eLpNorm' hQ0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_eLpNorm' hP0 ENNReal.ofReal_ne_top] at hb
  simp only [ENNReal.toReal_ofReal hQ.le,ENNReal.toReal_ofReal hp0.le] at hb
  simpa only [Φ,ψ,Z,wl,wm,H,E,F,Q,μ,←pow_mul,Nat.mul_comm,mul_assoc] using hb

/-- An actual source-PDE weighted-tail recurrence. Midpoint truncation keeps
the forcing term under control using only the preceding finite Lp tail. -/
theorem WeakPSourceSubsolutionPair.weighted_source_tail_step
    {n M : ℕ} {p c G K : ℝ} {Ω D : Set (Space n)}
    {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (hD : LocalDomain D Ω)
    (hη : SmoothTest D η) (hη0 : ∀ x,0≤η x) (hη1 : ∀ x,η x≤1)
    (hc : 0≤c) (hG : 0≤G) (hgrad : ∀ x∈D,‖gradient η x‖≤G)
    (hm : p≤(M : ℝ)) (hpn : p<(n : ℝ)) (hK1 : 1≤K) (j : ℕ) :
    eLpNorm' (fun x => η x^((M+1)^(j+1)-1)*
      max (u x-K*(1-(1/2 : ℝ)^(j+1))) 0) p (volume.restrict D) ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p : ℝ≥0∞) *
        ENNReal.ofReal ((((2 : ℝ)^p*(2*(M : ℝ)^p))*G^p+
          ((2 : ℝ)^p*p)*c*(4 : ℝ)^p)^p⁻¹) *
        ENNReal.ofReal (((M+1)^j : ℕ) : ℝ) * (ENNReal.ofReal (2 : ℝ))^(p/(n : ℝ)) *
        eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-K*(1-(1/2 : ℝ)^j)) 0)
          p (volume.restrict D) *
        (ENNReal.ofReal ((K*(1/2 : ℝ)^(j+1))⁻¹)*
          eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-K*(1-(1/2 : ℝ)^j)) 0)
            p (volume.restrict D))^(p/(n : ℝ)) := by
  let μ := volume.restrict D
  let r : ℕ := (M+1)^j
  let k0 : ℝ := K*(1-(1/2 : ℝ)^j)
  let k1 : ℝ := K*(1-(1/2 : ℝ)^(j+1))
  let m : ℝ := (k0+k1)/2
  let δ : ℝ := K*(1/2 : ℝ)^(j+1)
  let Z0 : Space n → ℝ := fun x => η x^(r-1)*max (u x-k0) 0
  let Zm : Space n → ℝ := fun x => η x^(r-1)*max (u x-m) 0
  let α : ℝ := p/(n : ℝ)
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hn0 : 0<(n : ℝ) := hp0.trans hpn
  have hα : 0<α := div_pos hp0 hn0
  have hK : 0<K := zero_lt_one.trans_le hK1
  have hδ : 0<δ := by dsimp only [δ];positivity
  have hgap : k1-k0=δ := by dsimp only [k0,k1,δ];rw [pow_succ];ring
  have hmid0 : m-k0=δ/2 := by dsimp only [m];linarith only [hgap]
  have hmid1 : k1-m=δ/2 := by dsimp only [m];linarith only [hgap]
  have hlm : k0<m := sub_pos.mp (by rw [hmid0];positivity)
  have hmh : m<k1 := sub_pos.mp (by rw [hmid1];positivity)
  have hδmid : m-k0=K*(1/2 : ℝ)^(j+2) := by
    rw [hmid0]
    dsimp only [δ]
    rw [show j+2=(j+1)+1 by omega,pow_succ]
    ring
  have hr : 0<r := pow_pos (Nat.zero_lt_succ M) j
  have hbase : (2 : ℝ)≤(M : ℝ)+1 := by linarith only [hm,hu.1]
  have hδpower : (m-k0)^(1-p)≤(4 : ℝ)^p*(r : ℝ)^p := by
    rw [hδmid]
    simpa only [r,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using
      regularity_source_delta_power j hu.1 hK1 hbase
  let Q : ℝ := (n : ℝ)*p/((n : ℝ)-p)
  have hd : 0<(n : ℝ)-p := sub_pos.mpr hpn
  have hpQ : p<Q := by dsimp only [Q];apply (lt_div_iff₀ hd).mpr;nlinarith
  have hrel : 1/p=1/Q+1/(n : ℝ) := by
    dsimp only [Q]
    field_simp [hp0.ne',hn0.ne',hd.ne'] <;>ring
  have hh := regularity_weighted_holder (M*r) (r-1) hp0 hpQ hpn hrel hmh
    (hu.2.2.1 D hD).2.1.1 hη.1.continuous.aestronglyMeasurable hη0 hη1
  have hs := regularity_source_midpoint_sobolev hu hD hη hη0 hη1 hc hG hgrad
    hr hm hpn hlm hδpower
  have hmono : eLpNorm' Zm p μ≤eLpNorm' Z0 p μ := by
    apply eLpNorm'_mono_ae hp0.le
    exact Eventually.of_forall (fun x => by
      have hz0 : 0≤Zm x := mul_nonneg (pow_nonneg (hη0 x) _) (le_max_right _ _)
      have hz1 : 0≤Z0 x := mul_nonneg (pow_nonneg (hη0 x) _) (le_max_right _ _)
      rw [Real.norm_eq_abs,abs_of_nonneg hz0,Real.norm_eq_abs,abs_of_nonneg hz1]
      exact mul_le_mul_of_nonneg_left
        (max_le_max (sub_le_sub_left hlm.le _) le_rfl) (pow_nonneg (hη0 x) _))
  have hgate : (ENNReal.ofReal ((k1-m)⁻¹)*eLpNorm' Zm p μ)^α ≤
      (ENNReal.ofReal ((k1-m)⁻¹)*eLpNorm' Z0 p μ)^α :=
    ENNReal.rpow_le_rpow (mul_le_mul_of_nonneg_left hmono bot_le) hα.le
  have hmain := hh.trans (mul_le_mul hs hgate bot_le bot_le)
  have hinv : (k1-m)⁻¹=2*δ⁻¹ := by rw [hmid1];field_simp [hδ.ne']
  have hgateeq : (ENNReal.ofReal ((k1-m)⁻¹)*eLpNorm' Z0 p μ)^α =
      (ENNReal.ofReal (2 : ℝ))^α*(ENNReal.ofReal δ⁻¹*eLpNorm' Z0 p μ)^α := by
    rw [hinv,ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),mul_assoc,
      ENNReal.mul_rpow_of_nonneg _ _ hα.le]
  have hsnext : M*r+(r-1)=(M+1)^(j+1)-1 := by
    dsimp only [r]
    rw [pow_succ',Nat.add_mul,Nat.one_mul]
    omega
  change eLpNorm' (fun x => η x^(M*r+(r-1))*max (u x-k1) 0) p μ ≤
    _*(ENNReal.ofReal ((k1-m)⁻¹)*eLpNorm' Z0 p μ)^α at hmain
  rw [hsnext,hgateeq] at hmain
  have hshuffle (a b c d : ℝ≥0∞) : a*b*(c*d)=a*c*b*d := by ring
  have hmain' := hmain.trans_eq (hshuffle _ _ _ _)
  simpa only [r,k0,k1,δ,Z0,μ,α] using hmain'

private theorem regularity_source_tail_finite {n : ℕ} {p : ℝ}
    {D : Set (Space n)} {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p D u g) (hDb : Bornology.IsBounded D)
    (hη : Continuous η) (hη0 : ∀ x,0≤η x) (hη1 : ∀ x,η x≤1)
    (s : ℕ) (k : ℝ) :
    eLpNorm' (fun x => η x^s*max (u x-k) 0) p (volume.restrict D)≠(∞ : ℝ≥0∞) := by
  have hz : SobolevPair p D (fun x => u x-k) g := by
    exact (hu.add (sobolevPair_const hu.1 hDb (-k))).congr
      (Eventually.of_forall (fun x => by simp [sub_eq_add_neg]))
      (Eventually.of_forall (fun x => by simp))
  have hm := hz.2.1.pos_part
  have htop : MemLp (fun x => η x^s) ∞ (volume.restrict D) :=
    memLp_top_of_bound (hη.pow s).aestronglyMeasurable 1
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (hη0 x) s)]
        exact pow_le_one₀ (hη0 x) (hη1 x)))
  have hf : MemLp (fun x => η x^s*max (u x-k) 0)
      (ENNReal.ofReal p) (volume.restrict D) := hm.mul' htop
  have hp0 : 0<p := zero_lt_one.trans hu.1
  simpa only [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hp0)
    ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hp0.le] using hf.2.ne

set_option maxHeartbeats 800000 in
private theorem regularity_source_upper_bound_cutoff
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)}
    {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (hD : LocalDomain D Ω)
    (hη : SmoothTest D η) (hη0 : ∀ x,0≤η x) (hη1 : ∀ x,η x≤1)
    (hc : 0≤c) (hpn : p<(n : ℝ)) :
    ∃ L : ℝ, 0<L ∧ ∀ᵐ x ∂volume.restrict D,η x=1 → u x≤L := by
  let μ := volume.restrict D
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hn0 : 0<(n : ℝ) := hp0.trans hpn
  have hα : 0<p/(n : ℝ) := div_pos hp0 hn0
  obtain ⟨M,hM⟩ := exists_nat_gt p
  have hm : p≤(M : ℝ) := hM.le
  obtain ⟨G0,hG0⟩ := (BMCompactCapacityV2.gradient_hasCompactSupport hη.2.1).exists_bound_of_continuous
    (BMCompactCapacityV2.continuous_gradient_of_contDiff hη.1)
  let G : ℝ := max G0 1
  have hG : 0≤G := zero_le_one.trans (le_max_right _ _)
  have hgrad (x : Space n) (_ : x∈D) : ‖gradient η x‖≤G := (hG0 x).trans (le_max_left _ _)
  let S : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p
  let E : ℝ := (2 : ℝ)^p*(2*(M : ℝ)^p)
  let F : ℝ := (2 : ℝ)^p*p
  let H : ℝ := E*G^p+F*c*(4 : ℝ)^p
  let C : ℝ := (S : ℝ)*H^p⁻¹*(2 : ℝ)^(p/(n : ℝ))
  have hH : 0≤H := by dsimp only [H,E,F];positivity
  have hC : 0≤C := mul_nonneg
    (mul_nonneg S.coe_nonneg (Real.rpow_nonneg hH _)) (Real.rpow_nonneg (by norm_num) _)
  let k : ℝ → ℕ → ℝ := fun K j => K*(1-(1/2 : ℝ)^j)
  let Y : ℝ → ℕ → ℝ := fun K j =>
    (eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-k K j) 0) p μ).toReal
  let N : ℝ := Y 1 0
  have hY0 (K : ℝ) (_ : 0<K) : Y K 0=N := by simp [Y,k,N]
  have hY (K : ℝ) (_ : 0<K) (j : ℕ) : 0≤Y K j := ENNReal.toReal_nonneg
  have hfinite (s : ℕ) (l : ℝ) :
      eLpNorm' (fun x => η x^s*max (u x-l) 0) p μ≠(∞ : ℝ≥0∞) :=
    regularity_source_tail_finite (hu.2.2.1 D hD) hD.2.1 hη.1.continuous hη0 hη1 s l
  have hstep (K : ℝ) (hK1 : 1≤K) (j : ℕ) :
      Y K (j+1)≤C*((M : ℝ)+1)^j*Y K j*
        (((K*((1/2 : ℝ)^(j+1)))⁻¹)*Y K j)^(p/(n : ℝ)) := by
    have hK : 0<K := zero_lt_one.trans_le hK1
    have hδp : 0<K*(1/2 : ℝ)^(j+1) := by positivity
    have he := hu.weighted_source_tail_step hD hη hη0 hη1 hc hG hgrad hm hpn hK1 j
    have hfin := hfinite ((M+1)^j-1) (k K j)
    have hright :
        (S*ENNReal.ofReal (H^p⁻¹)*ENNReal.ofReal (((M+1)^j : ℕ) : ℝ)*
          (ENNReal.ofReal (2 : ℝ))^(p/(n : ℝ))*
          eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-k K j) 0) p μ)*
          (ENNReal.ofReal ((K*(1/2 : ℝ)^(j+1))⁻¹)*
            eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-k K j) 0) p μ)^(p/(n : ℝ))≠(∞ : ℝ≥0∞) := by
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)
              ENNReal.ofReal_ne_top)
            (ENNReal.rpow_ne_top_of_nonneg hα.le ENNReal.ofReal_ne_top)) hfin)
        (ENNReal.rpow_ne_top_of_nonneg hα.le (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin))
    have ht := ENNReal.toReal_mono hright he
    simp only [ENNReal.toReal_mul,ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hH p⁻¹),
      ENNReal.toReal_ofReal (Nat.cast_nonneg ((M+1)^j)),
      ENNReal.toReal_ofReal (inv_nonneg.mpr hδp.le),←ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ)≤2)] at ht
    change Y K (j+1)≤(S : ℝ)*H^p⁻¹*
      ((((M+1)^j : ℕ) : ℝ))*(2 : ℝ)^(p/(n : ℝ))*Y K j*
      (((K*((1/2 : ℝ)^(j+1)))⁻¹)*Y K j)^(p/(n : ℝ)) at ht
    have hcoeff : (S : ℝ)*H^p⁻¹*((((M+1)^j : ℕ) : ℝ))*(2 : ℝ)^(p/(n : ℝ))=
        C*((M : ℝ)+1)^j := by
      dsimp only [C]
      simp only [Nat.cast_pow,Nat.cast_add,Nat.cast_one]
      ring
    rw [hcoeff] at ht
    exact ht
  obtain ⟨L,hL1,hlim⟩ := regularity_dyadic_tail_decay Y hC (by positivity : 0≤(M : ℝ)+1)
    hα (hY 1 zero_lt_one 0) hY hY0 hstep
  have hL : 0<L := zero_lt_one.trans_le hL1
  let F : Space n → ℝ := fun x => if η x=1 then max (u x-L) 0 else 0
  have hm : AEStronglyMeasurable (fun x => max (u x-L) 0) μ :=
    ((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      (hu.2.2.1 D hD).2.1.1
  have hF : AEStronglyMeasurable F μ :=
    hm.indicator (isClosed_eq hη.1.continuous continuous_const).measurableSet
  have hmono (j : ℕ) : eLpNorm' F p μ≤
      eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-k L j) 0) p μ := by
    apply eLpNorm'_mono_ae hp0.le
    exact Eventually.of_forall (fun x => by
      have hkL : k L j≤L := by
        dsimp only [k]
        nlinarith [pow_nonneg (show (0 : ℝ)≤1/2 by norm_num) j]
      by_cases hx : η x=1
      · simp only [F,if_pos hx,hx,one_pow,one_mul,Real.norm_eq_abs,
          abs_of_nonneg (le_max_right (u x-L) 0),
          abs_of_nonneg (le_max_right (u x-k L j) 0)]
        exact max_le_max (sub_le_sub_left hkL _) le_rfl
      · simp only [F,if_neg hx,norm_zero]
        exact norm_nonneg _)
  have hFfin : eLpNorm' F p μ≠(∞ : ℝ≥0∞) :=
    ((hmono 0).trans_lt (lt_top_iff_ne_top.mpr (hfinite _ _))).ne
  have hsmall (j : ℕ) : (eLpNorm' F p μ).toReal≤Y L j :=
    ENNReal.toReal_mono (hfinite _ _) (hmono j)
  have hzle := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hsmall)
  have hzreal : (eLpNorm' F p μ).toReal=0 := le_antisymm hzle ENNReal.toReal_nonneg
  have hz : eLpNorm' F p μ=0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hzreal with h|h
    · exact h
    · exact False.elim (hFfin h)
  have hae := (eLpNorm'_eq_zero_iff hp0 hF).mp hz
  refine ⟨L,hL,?_⟩
  filter_upwards [hae] with x hx
  intro hxη
  have he : max (u x-L) 0=0 := by simpa only [F,hxη,if_true,Pi.zero_apply] using hx
  exact sub_nonpos.mp ((le_max_left _ _).trans_eq he)

private theorem regularity_source_compact_cutoff {n : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K⊆Ω) :
    ∃ (D : Set (Space n)) (η : Space n → ℝ),LocalDomain D Ω ∧ K⊆D ∧
      SmoothTest D η ∧ (∀ x,0≤η x) ∧ (∀ x,η x≤1) ∧ (∀ x∈K,η x=1) := by
  obtain ⟨δ,hδ,hδΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let D := thickening δ K
  have hD : LocalDomain D Ω := ⟨isOpen_thickening,hK.isBounded.thickening,
    (closure_thickening_subset_cthickening δ K).trans hδΩ⟩
  have hKD : K⊆D := self_subset_thickening hδ K
  obtain ⟨f,hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hD.1 hKD
  let η : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hη : SmoothTest D η := ⟨Real.smoothTransition.contDiff.comp hf.1,
    hf.2.1.comp_left (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))),
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1⟩
  exact ⟨D,η,hD,hKD,hη,fun x => Real.smoothTransition.nonneg _,
    fun x => Real.smoothTransition.le_one _,fun x hx =>
      Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)⟩


/-- Actual local upper boundedness of a weak subsolution with a nonnegative
constant upper forcing bound. The full source contribution is derived above. -/
theorem WeakPSourceSubsolutionPair.exists_ae_upper_bound_compact
    {n : ℕ} {p c : ℝ} {Ω K : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (hc : 0≤c)
    (hpn : p<(n : ℝ)) (hK : IsCompact K) (hKΩ : K⊆Ω) :
    ∃ L : ℝ,0<L ∧ ∀ᵐ x ∂volume.restrict K,u x≤L := by
  obtain ⟨D,η,hD,hKD,hη,hη0,hη1,hηK⟩ := regularity_source_compact_cutoff hu.2.1 hK hKΩ
  obtain ⟨L,hL,hae⟩ := regularity_source_upper_bound_cutoff hu hD hη hη0 hη1 hc hpn
  refine ⟨L,hL,?_⟩
  have ht := ae_restrict_of_ae_restrict_of_subset hKD hae
  filter_upwards [ht,ae_restrict_mem hK.measurableSet] with x hx hxK
  exact hx (hηK x hxK)

private theorem regularity_source_subsolution_increase
    {n : ℕ} {p c d : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (hcd : c≤d) :
    WeakPSourceSubsolutionPair p d Ω u g := by
  refine ⟨hu.1,hu.2.1,hu.2.2.1,?_⟩
  intro D hD θ h hθ hθ0
  obtain ⟨hi,he⟩ := hu.2.2.2 D hD θ h hθ hθ0
  exact ⟨hi,he.trans (mul_le_mul_of_nonneg_right hcd
    (show 0≤∫ x in D,θ x from integral_nonneg_of_ae hθ0))⟩

private theorem regularity_source_pair_neg
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) :
    WeakPSourcePair p (-c) Ω (fun x => -u x) (fun x => -g x) := by
  refine ⟨hu.1,hu.2.1,?_,?_⟩
  · intro D hD
    have hs := (hu.2.2.1 D hD).smul (-1)
    exact hs.congr (Eventually.of_forall (fun x => by simp))
      (Eventually.of_forall (fun x => by simp))
  · intro D hD θ h hθ
    obtain ⟨hi,he⟩ := hu.2.2.2 D hD θ h hθ
    have hflux : fluxPairing p (fun x => -g x) h = -fluxPairing p g h := by
      funext x
      simp only [fluxPairing,pFlux_neg,inner_neg_left,Pi.neg_apply]
    rw [hflux]
    refine ⟨hi.neg,?_⟩
    simp only [Pi.neg_apply]
    rw [integral_neg,he]
    ring

/-- Actual compact-set L-infinity membership for a constant-source weak
solution, for 1<p<n. Both signs are bounded by the actual source |c|; no
continuous/classical representative or a priori u bound is an input. -/
theorem WeakPSourcePair.memLp_top_compact
    {n : ℕ} {p c : ℝ} {Ω K : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hpn : p<(n : ℝ))
    (hK : IsCompact K) (hKΩ : K⊆Ω) :
    MemLp u ∞ (volume.restrict K) := by
  have hplus : WeakPSourceSubsolutionPair p |c| Ω u g :=
    regularity_source_subsolution_increase hu.subsolution (le_abs_self c)
  have hneg := regularity_source_pair_neg hu
  have hminus : WeakPSourceSubsolutionPair p |c| Ω (fun x => -u x) (fun x => -g x) :=
    regularity_source_subsolution_increase hneg.subsolution
      (by simpa only [abs_neg] using le_abs_self (-c))
  obtain ⟨U,hU,ha⟩ := hplus.exists_ae_upper_bound_compact (abs_nonneg c) hpn hK hKΩ
  obtain ⟨V,hV,hb⟩ := hminus.exists_ae_upper_bound_compact (abs_nonneg c) hpn hK hKΩ
  obtain ⟨D,η,hD,hKD,hη,-,-,-⟩ := regularity_source_compact_cutoff hu.2.1 hK hKΩ
  have hm := (MemLp.mono_measure (Measure.restrict_mono_set volume hKD)
    (hu.2.2.1 D hD).2.1).1
  apply memLp_top_of_bound hm (max U V)
  filter_upwards [ha,hb] with x hx hy
  change -u x≤V at hy
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have ht : V≤max U V := le_max_right _ _
    linarith
  · exact hx.trans (le_max_left _ _)

end BMCompactPDE

end RegularityBody_RegularitySourceBounded

#print axioms BMCompactPDE.WeakPSourceSubsolutionPair.caccioppoli_upper_natPow_source
#print axioms BMCompactPDE.WeakPSourceSubsolutionPair.weighted_source_tail_step
#print axioms BMCompactPDE.WeakPSourceSubsolutionPair.exists_ae_upper_bound_compact
#print axioms BMCompactPDE.WeakPSourcePair.memLp_top_compact
