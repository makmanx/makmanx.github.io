import RegularitySourceBatch

/-! A uniform actual source-PDE small-tail criterion. The positive threshold
is chosen from p,n,source cap and geometric derivative cap BEFORE domain,
cutoff, function and weak field. Source monotonicity is derived on actual
full-W0 tests; no bound on the input solution or oscillation class is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

private theorem continuous_uniform_tail_finite {n : ℕ} {p : ℝ}
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
theorem exists_uniform_source_small_tail_threshold
    {n : ℕ} {p c G : ℝ} (hp : 1<p) (hc : 0≤c) (hG : 0≤G) (hpn : p<(n : ℝ)) :
    ∃ ε : ℝ,0<ε ∧ ∀ (Ω D : Set (Space n)) (η : Space n → ℝ),
      LocalDomain D Ω → SmoothTest D η → (∀ x,0≤η x) → (∀ x,η x≤1) →
      (∀ x∈D,‖gradient η x‖≤G) →
      ∀ (d : ℝ) (u : Space n → ℝ) (g : Space n → Space n),d≤c →
      WeakPSourceSubsolutionPair p d Ω u g →
      (eLpNorm' (fun x => max (u x) 0) p (volume.restrict D)).toReal≤ε →
      ∀ᵐ x ∂volume.restrict D,η x=1 → u x≤1 := by
  have hp0 : 0<p := zero_lt_one.trans hp
  have hn0 : 0<(n : ℝ) := hp0.trans hpn
  have hα : 0<p/(n : ℝ) := div_pos hp0 hn0
  obtain ⟨M,hM⟩ := exists_nat_gt p
  have hm : p≤(M : ℝ) := hM.le
  let S : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) p
  let E : ℝ := (2 : ℝ)^p*(2*(M : ℝ)^p)
  let F : ℝ := (2 : ℝ)^p*p
  let H : ℝ := E*G^p+F*c*(4 : ℝ)^p
  let C : ℝ := (S : ℝ)*H^p⁻¹*(2 : ℝ)^(p/(n : ℝ))
  have hH : 0≤H := by dsimp only [H,E,F];positivity
  have hC : 0≤C := mul_nonneg
    (mul_nonneg S.coe_nonneg (Real.rpow_nonneg hH _)) (Real.rpow_nonneg (by norm_num) _)
  let α : ℝ := p/(n : ℝ)
  let A : ℝ := 1+C*(2 : ℝ)^α
  let B : ℝ := max 1 (((M : ℝ)+1)*(2 : ℝ)^α)
  have hA : 0<A := by dsimp only [A];positivity
  have hB : 1≤B := le_max_left _ _
  obtain ⟨ε,hε,hdecay⟩ := regularity_superlinear_decay hA hB hα
  refine ⟨ε,hε,?_⟩
  intro Ω D η hD hη hη0 hη1 hgrad d u g hd huRaw hsmallinit
  let μ := volume.restrict D
  have hu : WeakPSourceSubsolutionPair p c Ω u g := by
    refine ⟨huRaw.1,huRaw.2.1,huRaw.2.2.1,?_⟩
    intro U hU θ h hθ hθ0
    obtain ⟨hi,he⟩ := huRaw.2.2.2 U hU θ h hθ hθ0
    exact ⟨hi,he.trans (mul_le_mul_of_nonneg_right hd (integral_nonneg_of_ae hθ0))⟩
  let k : ℝ → ℕ → ℝ := fun K j => K*(1-(1/2 : ℝ)^j)
  let Y : ℝ → ℕ → ℝ := fun K j =>
    (eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-k K j) 0) p μ).toReal
  let N : ℝ := Y 1 0
  have hY0 (K : ℝ) (_ : 0<K) : Y K 0=N := by simp [Y,k,N]
  have hY (K : ℝ) (_ : 0<K) (j : ℕ) : 0≤Y K j := ENNReal.toReal_nonneg
  have hfinite (s : ℕ) (l : ℝ) :
      eLpNorm' (fun x => η x^s*max (u x-l) 0) p μ≠(∞ : ℝ≥0∞) :=
    continuous_uniform_tail_finite (hu.2.2.1 D hD) hD.2.1 hη.1.continuous hη0 hη1 s l
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
  have hinit : Y 1 0≤ε := by simpa [Y,k] using hsmallinit
  have hYstep (j : ℕ) : Y 1 (j+1)≤A*B^j*(Y 1 j)^(1+α) := by
    have hs := hstep 1 le_rfl j
    have hinv : (((1/2 : ℝ)^(j+1)))⁻¹=(2 : ℝ)^(j+1) := by
      rw [←inv_pow]
      norm_num
    rw [one_mul,hinv] at hs
    have hfac : C*((M : ℝ)+1)^j*Y 1 j*((2 : ℝ)^(j+1)*Y 1 j)^α =
        (C*(2 : ℝ)^α)*(((M : ℝ)+1)*(2 : ℝ)^α)^j*(Y 1 j)^(1+α) := by
      by_cases hz : Y 1 j=0
      · simp [hz,Real.zero_rpow hα.ne',Real.zero_rpow (by linarith : 1+α≠0)]
      · have hpos : 0<Y 1 j := (hY 1 zero_lt_one j).lt_of_ne' hz
        rw [Real.mul_rpow (by positivity : 0≤(2 : ℝ)^(j+1)) (hY 1 zero_lt_one j),
          ←Real.rpow_pow_comm (by norm_num : (0 : ℝ)≤2) α (j+1),
          pow_succ,mul_pow,Real.rpow_add hpos,Real.rpow_one]
        ring
    change Y 1 (j+1)≤C*((M : ℝ)+1)^j*Y 1 j*((2 : ℝ)^(j+1)*Y 1 j)^α at hs
    rw [hfac] at hs
    have hCA : C*(2 : ℝ)^α≤A := by dsimp only [A];linarith
    have hBB : ((M : ℝ)+1)*(2 : ℝ)^α≤B := le_max_right _ _
    have hnon : 0≤((M : ℝ)+1)*(2 : ℝ)^α := by positivity
    have hpow : (((M : ℝ)+1)*(2 : ℝ)^α)^j≤B^j :=
      pow_le_pow_left₀ hnon hBB j
    exact hs.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul hCA hpow (pow_nonneg hnon j) hA.le)
      (Real.rpow_nonneg (hY 1 zero_lt_one j) _))
  have hlim := hdecay (Y 1) (hY 1 zero_lt_one) hinit hYstep
  let F : Space n → ℝ := fun x => if η x=1 then max (u x-1) 0 else 0
  have hm : AEStronglyMeasurable (fun x => max (u x-1) 0) μ :=
    ((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable
      (hu.2.2.1 D hD).2.1.1
  have hF : AEStronglyMeasurable F μ :=
    hm.indicator (isClosed_eq hη.1.continuous continuous_const).measurableSet
  have hmono (j : ℕ) : eLpNorm' F p μ≤
      eLpNorm' (fun x => η x^((M+1)^j-1)*max (u x-k 1 j) 0) p μ := by
    apply eLpNorm'_mono_ae hp0.le
    exact Eventually.of_forall (fun x => by
      have hkL : k 1 j≤1 := by
        dsimp only [k]
        nlinarith [pow_nonneg (show (0 : ℝ)≤1/2 by norm_num) j]
      by_cases hx : η x=1
      · simp only [F,if_pos hx,hx,one_pow,one_mul,Real.norm_eq_abs,
          abs_of_nonneg (le_max_right (u x-1) 0),
          abs_of_nonneg (le_max_right (u x-k 1 j) 0)]
        exact max_le_max (sub_le_sub_left hkL _) le_rfl
      · simp only [F,if_neg hx,norm_zero]
        exact norm_nonneg _)
  have hFfin : eLpNorm' F p μ≠(∞ : ℝ≥0∞) :=
    ((hmono 0).trans_lt (lt_top_iff_ne_top.mpr (hfinite _ _))).ne
  have hsmall (j : ℕ) : (eLpNorm' F p μ).toReal≤Y 1 j :=
    ENNReal.toReal_mono (hfinite _ _) (hmono j)
  have hzle := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hsmall)
  have hzreal : (eLpNorm' F p μ).toReal=0 := le_antisymm hzle ENNReal.toReal_nonneg
  have hz : eLpNorm' F p μ=0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp hzreal with h|h
    · exact h
    · exact False.elim (hFfin h)
  have hae := (eLpNorm'_eq_zero_iff hp0 hF).mp hz
  filter_upwards [hae] with x hx
  intro hxη
  have he : max (u x-1) 0=0 := by simpa only [F,hxη,if_true,Pi.zero_apply] using hx
  exact sub_nonpos.mp ((le_max_left _ _).trans_eq he)

end BMCompactPDE
#print axioms BMCompactPDE.exists_uniform_source_small_tail_threshold
