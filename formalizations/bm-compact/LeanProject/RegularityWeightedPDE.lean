import RegularityWeightedHolder
import PotentialDeGiorgiStep

/-! Actual weighted De Giorgi tails for arbitrary weak subsolutions. The only
norm bound supplied below is on the chosen smooth cutoff gradient; no upper
bound, continuity or classical differentiability of the weak input is assumed.
The cutoff powers are genuine full-W0 tests from the checked preceding stage. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

private theorem regularity_weighted_memLp {n : ℕ} {p : ℝ}
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

/-- Uniform Sobolev-Caccioppoli control for the actual family eta^r. The old
unweighted moment is replaced by the preceding weighted Lp tail through the
actual derivative of eta^r, with its explicit linear factor r. -/
theorem WeakPSubsolutionPair.weighted_cutoff_sobolev
    {n M r : ℕ} {p G : ℝ} {Ω D : Set (Space n)}
    {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hD : LocalDomain D Ω)
    (hη : SmoothTest D η) (hη0 : ∀ x,0≤η x) (hη1 : ∀ x,η x≤1)
    (hG : 0≤G) (hgrad : ∀ x∈D,‖gradient η x‖≤G)
    (hr : 0<r) (hm : p≤(M : ℝ)) (hpn : p<(n : ℝ)) (k : ℝ) :
    eLpNorm' (fun x => η x^(M*r)*max (u x-k) 0)
      ((n : ℝ)*p/((n : ℝ)-p)) (volume.restrict D) ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p : ℝ≥0∞) *
        ENNReal.ofReal (((2 : ℝ)^p*(2*(M : ℝ)^p)) ^ p⁻¹) *
        ENNReal.ofReal ((r : ℝ)*G) *
        eLpNorm' (fun x => η x^(r-1)*max (u x-k) 0) p (volume.restrict D) := by
  let μ := volume.restrict D
  let ψ : Space n → ℝ := fun x => η x^r
  let w : Space n → ℝ := fun x => max (u x-k) 0
  let Z : Space n → ℝ := fun x => η x^(r-1)*w x
  let W : Space n → ℝ := fun x => w x*‖gradient ψ x‖
  let E : ℝ := (2 : ℝ)^p*(2*(M : ℝ)^p)
  let Q : ℝ := (n : ℝ)*p/((n : ℝ)-p)
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hn0 : 0<(n : ℝ) := hp0.trans hpn
  have hQ : 0<Q := div_pos (mul_pos hn0 hp0) (sub_pos.mpr hpn)
  have hP0 : ENNReal.ofReal p≠0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hQ0 : ENNReal.ofReal Q≠0 := ENNReal.ofReal_ne_zero_iff.mpr hQ
  have hψ : SmoothTest D ψ := hη.natPow_cutoff hr.ne'
  have hψ0 (x : Space n) : 0≤ψ x := pow_nonneg (hη0 x) r
  have hψ1 (x : Space n) : ψ x≤1 := pow_le_one₀ (hη0 x) (hη1 x)
  have hwm : MemLp w (ENNReal.ofReal p) μ := by
    simpa [w,μ] using regularity_weighted_memLp (hu.2.2.1 D hD) hD.2.1
      hη.1.continuous hη0 hη1 0 k
  have hgtop : MemLp (fun x => ‖gradient ψ x‖) ∞ μ :=
    ((BMCompactCapacityV2.continuous_gradient_of_contDiff hψ.1).memLp_top_of_hasCompactSupport
      (BMCompactCapacityV2.gradient_hasCompactSupport hψ.2.1) μ).norm
  have hW : MemLp W (ENNReal.ofReal p) μ := hgtop.smul hwm
  have hE : 0≤E := by dsimp only [E];positivity
  have hI : 0≤∫ x,‖W x‖^p ∂μ :=
    integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have hmoment : (∫ x in D,w x^p*‖gradient ψ x‖^p)=∫ x,‖W x‖^p ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      dsimp only [W]
      rw [Real.norm_eq_abs,abs_of_nonneg
        (mul_nonneg (le_max_right (u x-k) 0) (norm_nonneg _)),
        Real.mul_rpow (le_max_right (u x-k) 0) (norm_nonneg _)])
  have hWeq := hW.eLpNorm_eq_integral_rpow_norm hP0 ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal hp0.le] at hWeq
  have hbase := hu.truncated_sobolev_bound hD hψ hψ0 hψ1 hm hpn k
  change eLpNorm (fun x => ψ x^M*w x) (ENNReal.ofReal Q) μ ≤
    _*ENNReal.ofReal ((E*(∫ x in D,w x^p*‖gradient ψ x‖^p))^p⁻¹) at hbase
  rw [hmoment,Real.mul_rpow hE hI,
    ENNReal.ofReal_mul (Real.rpow_nonneg hE _),←hWeq] at hbase
  have hWZ : eLpNorm W (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal ((r : ℝ)*G)*eLpNorm Z (ENNReal.ofReal p) μ := by
    have hc : 0≤(r : ℝ)*G := mul_nonneg (Nat.cast_nonneg _) hG
    rw [←Real.enorm_eq_ofReal hc,←eLpNorm_const_smul ((r : ℝ)*G) Z]
    apply eLpNorm_mono_ae
    filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hxD
    have hw0 : 0≤w x := le_max_right _ _
    have hz0 : 0≤Z x := mul_nonneg (pow_nonneg (hη0 x) _) hw0
    have hd : gradient ψ x=((r : ℝ)*η x^(r-1)) • gradient η x :=
      gradient_natPow_cutoff (hη.1.differentiable (by simp)) r x
    have hcoef : 0≤(r : ℝ)*η x^(r-1) :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hη0 x) _)
    change ‖w x*‖gradient ψ x‖‖≤‖((r : ℝ)*G) • Z x‖
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hw0 (norm_nonneg _)),
      norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,
      Real.norm_eq_abs,abs_of_nonneg hz0]
    change w x*‖gradient ψ x‖≤((r : ℝ)*G)*(η x^(r-1)*w x)
    rw [hd,norm_smul,Real.norm_eq_abs,abs_of_nonneg hcoef]
    nlinarith [mul_le_mul_of_nonneg_left (hgrad x hxD)
      (mul_nonneg hw0 hcoef)]
  have hb := hbase.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hWZ bot_le) bot_le)
  rw [eLpNorm_eq_eLpNorm' hQ0 ENNReal.ofReal_ne_top,
    eLpNorm_eq_eLpNorm' hP0 ENNReal.ofReal_ne_top] at hb
  simp only [ENNReal.toReal_ofReal hp0.le,ENNReal.toReal_ofReal hQ.le] at hb
  simpa only [ψ,Z,w,E,μ,Q,←pow_mul,Nat.mul_comm,mul_assoc] using hb

/-- A genuine superlinear weighted-tail step from the actual weak equation.
The function u may be unbounded. The next cutoff power is r*(M+1)-1 when r>0. -/
theorem WeakPSubsolutionPair.weighted_tail_step
    {n M r : ℕ} {p G k h : ℝ} {Ω D : Set (Space n)}
    {u η : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hD : LocalDomain D Ω)
    (hη : SmoothTest D η) (hη0 : ∀ x,0≤η x) (hη1 : ∀ x,η x≤1)
    (hG : 0≤G) (hgrad : ∀ x∈D,‖gradient η x‖≤G)
    (hr : 0<r) (hm : p≤(M : ℝ)) (hpn : p<(n : ℝ)) (hkh : k<h) :
    eLpNorm' (fun x => η x^(M*r+(r-1))*max (u x-h) 0) p (volume.restrict D) ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p : ℝ≥0∞) *
        ENNReal.ofReal (((2 : ℝ)^p*(2*(M : ℝ)^p)) ^ p⁻¹) *
        ENNReal.ofReal ((r : ℝ)*G) *
        eLpNorm' (fun x => η x^(r-1)*max (u x-k) 0) p (volume.restrict D) *
        (ENNReal.ofReal ((h-k)⁻¹)*
          eLpNorm' (fun x => η x^(r-1)*max (u x-k) 0) p (volume.restrict D)) ^
            (p/(n : ℝ)) := by
  let Q : ℝ := (n : ℝ)*p/((n : ℝ)-p)
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hn0 : 0<(n : ℝ) := hp0.trans hpn
  have hd : 0<(n : ℝ)-p := sub_pos.mpr hpn
  have hpQ : p<Q := by
    dsimp only [Q]
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  have he : 1/p=1/Q+1/(n : ℝ) := by
    dsimp only [Q]
    field_simp [hp0.ne',hn0.ne',hd.ne']
    <;>ring
  have hh := regularity_weighted_holder (M*r) (r-1) hp0 hpQ hpn he hkh
    (hu.2.2.1 D hD).2.1.1 hη.1.continuous.aestronglyMeasurable hη0 hη1
  have hs := hu.weighted_cutoff_sobolev hD hη hη0 hη1 hG hgrad hr hm hpn k
  exact hh.trans (mul_le_mul_of_nonneg_right hs bot_le)

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSubsolutionPair.weighted_cutoff_sobolev
#print axioms BMCompactPDE.WeakPSubsolutionPair.weighted_tail_step
