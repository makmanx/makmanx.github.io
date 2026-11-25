import PotentialTruncatedEnergy
import PotentialSobolevBoost
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

/-! Actual one-step DeGiorgi estimates: the genuine truncation test is put
through critical Sobolev, its actual gradient energy is controlled by the weak
equation, and Chebyshev bounds inner superlevels. No oscillation/Harnack or
selected C1/Holder-gradient conclusion is assumed or claimed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

private def potentialLevelEnergy {n : ℕ} (p : ℝ) (M : ℕ) (η u : Space n → ℝ)
    (g : Space n → Space n) (k : ℝ) : Space n → ℝ :=
  fun x => if k<u x then η x^M*‖g x‖^p else 0

private def potentialLevelMoment {n : ℕ} (p : ℝ) (η u : Space n → ℝ) (k : ℝ) : Space n → ℝ :=
  fun x => (max (u x-k) 0)^p*‖gradient η x‖^p

private def potentialCutoffField {n : ℕ} (M : ℕ) (η u : Space n → ℝ)
    (g : Space n → Space n) (k : ℝ) : Space n → Space n :=
  fun x => if k<u x then
    η x^M • g x+((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x else 0

private theorem potential_norm_add_rpow_le {n : ℕ} {p : ℝ} (hp : 0≤p)
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

private theorem potential_cutoff_energy_pointwise {n M : ℕ} {p : ℝ}
    (hp : 1<p) {η u : Space n → ℝ} {g : Space n → Space n}
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1) (k : ℝ) (x : Space n) :
    ‖potentialCutoffField M η u g k x‖^p ≤
      (2 : ℝ)^p*(potentialLevelEnergy p M η u g k x+
        (M : ℝ)^p*potentialLevelMoment p η u k x) := by
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
    have hh := potential_norm_add_rpow_le hp0.le
      (η x^M • g x) (((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x)
    simp only [potentialCutoffField,potentialLevelEnergy,potentialLevelMoment,
      if_pos hx,max_eq_left hz.le]
    exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add hA (by
      simpa only [mul_assoc] using hB)) (Real.rpow_nonneg (by norm_num) p))
  · have hz : u x-k≤0 := sub_nonpos.mpr (le_of_not_gt hx)
    simp [potentialCutoffField,potentialLevelEnergy,potentialLevelMoment,hx,
      max_eq_right hz,Real.zero_rpow hp0.ne']

private theorem potential_level_energy_integrable {n M : ℕ} {p : ℝ}
    {D : Set (Space n)} {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p D u g) (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1) (k : ℝ) :
    Integrable (potentialLevelEnergy p M η u g k) (volume.restrict D) := by
  have hGI := integrable_norm_rpow_of_memLp hu.1 hu.2.2.1
  have hi : Integrable (fun x => η x^M*‖g x‖^p) (volume.restrict D) := by
    apply hGI.mono_nonneg ((hη.1.continuous.pow M).aestronglyMeasurable.mul hGI.1)
    · exact Eventually.of_forall (fun x => mul_nonneg
        (pow_nonneg (hη0 x) M) (Real.rpow_nonneg (norm_nonneg _) _))
    · exact Eventually.of_forall (fun x =>
        (mul_le_mul_of_nonneg_right (pow_le_one₀ (hη0 x) (hη1 x))
          (Real.rpow_nonneg (norm_nonneg (g x)) p)).trans_eq (one_mul _))
  exact hi.indicator₀ (nullMeasurableSet_lt aemeasurable_const hu.2.1.1.aemeasurable)

private theorem potential_level_moment_integrable {n : ℕ} {p : ℝ}
    {D : Set (Space n)} {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p D u g) (hDb : Bornology.IsBounded D)
    (hη : SmoothTest D η) (k : ℝ) :
    Integrable (potentialLevelMoment p η u k) (volume.restrict D) := by
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
      potentialLevelMoment p η u k := by
    funext x
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (le_max_right (u x-k) 0),
      Real.mul_rpow (le_max_right _ _) (norm_nonneg _)]
    rfl
  rw [he] at hi
  exact hi

/-- The actual weak field of the truncated cutoff has controlled p-energy.
This bridges the signed Caccioppoli estimate to the critical Sobolev bound. -/
theorem WeakPSubsolutionPair.cutoff_gradient_energy
    {n M : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1)
    (hm : p≤(M : ℝ)) (k : ℝ) :
    (∫ x in D, ‖if k<u x then
        η x^M • g x+((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x else 0‖^p) ≤
      ((2 : ℝ)^p*(2*(M : ℝ)^p)) *
        ∫ x in D, (max (u x-k) 0)^p*‖gradient η x‖^p := by
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hM2 : 2≤M := by exact_mod_cast hu.1.trans_le hm
  have hs := hu.2.2.1 D hD
  have hw := hs.upperCutoff_zeroBoundary hD.1 hD.2.1 hη hη0 hM2 k
  let A := potentialLevelEnergy p M η u g k
  let B := potentialLevelMoment p η u k
  let W := potentialCutoffField M η u g k
  have hAI : Integrable A (volume.restrict D) := potential_level_energy_integrable hs hη hη0 hη1 k
  have hBI : Integrable B (volume.restrict D) := potential_level_moment_integrable hs hD.2.1 hη k
  have hWI : Integrable (fun x => ‖W x‖^p) (volume.restrict D) :=
    integrable_norm_rpow_of_memLp hu.1 hw.1.2.2.1
  have hi := integral_mono hWI
    ((hAI.add (hBI.const_mul ((M : ℝ)^p))).const_mul ((2 : ℝ)^p))
    (fun x => potential_cutoff_energy_pointwise hu.1 hη0 hη1 k x)
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add hAI (hBI.const_mul ((M : ℝ)^p)),
    integral_const_mul] at hi
  have hc := hu.caccioppoli_upper_natPow hD hη hη0 hη1 hm k
  change (∫ x in D, A x) ≤ (M : ℝ)^p*∫ x in D, B x at hc
  have hh := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (by norm_num : (0 : ℝ)≤2) p)
  change (∫ x in D, ‖W x‖^p) ≤ ((2 : ℝ)^p*(2*(M : ℝ)^p))*(∫ x in D, B x)
  nlinarith

/-- A genuine one-step Sobolev-Caccioppoli estimate for the positive cutoff.
All norms are of the actual weak representative, not classical fderiv(u). -/
theorem WeakPSubsolutionPair.truncated_sobolev_bound
    {n M : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1)
    (hm : p≤(M : ℝ)) (hpn : p<(n : ℝ)) (k : ℝ) :
    eLpNorm (fun x => η x^M*max (u x-k) 0)
      (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) (volume.restrict D) ≤
      eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p *
        ENNReal.ofReal ((((2 : ℝ)^p*(2*(M : ℝ)^p)) *
          (∫ x in D, (max (u x-k) 0)^p*‖gradient η x‖^p)) ^ p⁻¹) := by
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hM2 : 2≤M := by exact_mod_cast hu.1.trans_le hm
  have hw := (hu.2.2.1 D hD).upperCutoff_zeroBoundary hD.1 hD.2.1 hη hη0 hM2 k
  have hb := (hw.critical_sobolev_explicit hpn).2
  have hP0 : ENNReal.ofReal p≠0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have he := MemLp.eLpNorm_eq_integral_rpow_norm hP0 ENNReal.ofReal_ne_top hw.1.2.2.1
  simp only [ENNReal.toReal_ofReal hp0.le] at he
  have hgrad : eLpNorm (fun x => if k<u x then
      η x^M • g x+((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x else 0)
      (ENNReal.ofReal p) (volume.restrict D) ≤
      ENNReal.ofReal ((((2 : ℝ)^p*(2*(M : ℝ)^p)) *
        (∫ x in D, (max (u x-k) 0)^p*‖gradient η x‖^p)) ^ p⁻¹) := by
    rw [he]
    apply ENNReal.ofReal_le_ofReal
    exact Real.rpow_le_rpow
      (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
      (hu.cutoff_gradient_energy hD hη hη0 hη1 hm k) (inv_nonneg.mpr hp0.le)
  exact hb.trans (mul_le_mul_of_nonneg_left hgrad (show
    0≤(eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p : ℝ≥0∞) from bot_le))

/-- Actual inner superlevel bound, the one-step nonlinear estimate used in
DeGiorgi iteration. The cutoff is genuinely smooth and equals one on K. -/
theorem WeakPSubsolutionPair.superlevel_step
    {n M : ℕ} {p k h : ℝ} {Ω D K : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1)
    (hηK : ∀ x∈K, η x=1) (hm : p≤(M : ℝ)) (hpn : p<(n : ℝ)) (hkh : k<h) :
    (ENNReal.ofReal (h-k)) ^ ((n : ℝ)*p/((n : ℝ)-p)) *
        (volume.restrict D) (K ∩ {x | h≤u x}) ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p *
        ENNReal.ofReal ((((2 : ℝ)^p*(2*(M : ℝ)^p)) *
          (∫ x in D, (max (u x-k) 0)^p*‖gradient η x‖^p)) ^ p⁻¹)) ^
        ((n : ℝ)*p/((n : ℝ)-p)) := by
  let Q : ℝ := (n : ℝ)*p/((n : ℝ)-p)
  let θ : Space n → ℝ := fun x => η x^M*max (u x-k) 0
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hn0 : 0<(n : ℝ) := hp0.trans hpn
  have hQ0 : 0<Q := div_pos (mul_pos hn0 hp0) (sub_pos.mpr hpn)
  have hM2 : 2≤M := by exact_mod_cast hu.1.trans_le hm
  have hw := (hu.2.2.1 D hD).upperCutoff_zeroBoundary hD.1 hD.2.1 hη hη0 hM2 k
  have hsubset : K ∩ {x | h≤u x} ⊆ {x | ENNReal.ofReal (h-k)≤‖θ x‖ₑ} := by
    intro x hx
    change ENNReal.ofReal (h-k)≤‖η x^M*max (u x-k) 0‖ₑ
    rw [hηK x hx.1,one_pow,one_mul]
    have he : h-k≤‖max (u x-k) 0‖ := by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
      exact (sub_le_sub_right hx.2 k).trans (le_max_left _ _)
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal he
  have hcheb := mul_meas_ge_le_pow_eLpNorm' (volume.restrict D)
    (ENNReal.ofReal_ne_zero_iff.mpr hQ0) ENNReal.ofReal_ne_top
    hw.1.2.1.1 (ENNReal.ofReal (h-k))
  simp only [ENNReal.toReal_ofReal hQ0.le] at hcheb
  have hmset : (ENNReal.ofReal (h-k))^Q*(volume.restrict D) (K ∩ {x | h≤u x}) ≤
      (ENNReal.ofReal (h-k))^Q*(volume.restrict D) {x | ENNReal.ofReal (h-k)≤‖θ x‖ₑ} :=
    mul_le_mul_of_nonneg_left (measure_mono hsubset) bot_le
  have hb := hu.truncated_sobolev_bound hD hη hη0 hη1 hm hpn k
  exact (hmset.trans hcheb).trans (ENNReal.rpow_le_rpow hb hQ0.le)

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSubsolutionPair.cutoff_gradient_energy
#print axioms BMCompactPDE.WeakPSubsolutionPair.truncated_sobolev_bound
#print axioms BMCompactPDE.WeakPSubsolutionPair.superlevel_step
