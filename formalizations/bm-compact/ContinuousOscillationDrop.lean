import ContinuousLevelEnergyBatch
import ContinuousUniformSmallTail
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Actual one-sided fixed-unit De Giorgi oscillation drop. Normalized upper
boundedness and the low-half measure are explicit intermediate data. They must
be derived/selected when this lemma is applied to arbitrary weak solutions.
-/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal
namespace BMCompactPDE

/- Retained exact private V8 negation proof; renamed helper only. -/
private theorem continuous_source_pair_neg
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


private theorem continuous_small_ball_measure_le_cube (n : ℕ) :
    (volume : Measure (Space n)).restrict (ball 0 (3/4 : ℝ)) ≤
      ((2 : ℝ≥0∞)^n) • continuousCubeMeasure n := by
  have hs : ball (0 : Space n) (3/4 : ℝ)⊆continuousUnitCube n :=
    (ball_subset_ball (by norm_num : (3/4 : ℝ)≤1)).trans (continuous_ball_one_subset_cube n)
  have he : ((2 : ℝ≥0∞)^n) • continuousCubeMeasure n=
      volume.restrict (continuousUnitCube n) := by
    rw [continuousCubeMeasure_eq,smul_smul,←mul_pow,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_pow,one_smul]
  exact (Measure.restrict_mono_set volume hs).trans_eq he.symm

private theorem continuous_normalized_tail_norm_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {u : α → ℝ} {p τ : ℝ}
    (hp : 0<p) (hτ : 0<τ) (hu : AEMeasurable u μ)
    (hupper : ∀ᵐ x ∂μ,u x≤1) :
    eLpNorm' (fun x => max ((2/τ)*(u x-(1-τ))) 0) p μ ≤
      ENNReal.ofReal 2*(μ {x | 1-τ<u x})^(1/p) := by
  classical
  let H := {x | 1-τ<u x}
  have hH : NullMeasurableSet H μ := nullMeasurableSet_lt aemeasurable_const hu
  have ha : 0<2/τ := div_pos (by norm_num) hτ
  have hm : eLpNorm (fun x => max ((2/τ)*(u x-(1-τ))) 0) (ENNReal.ofReal p) μ ≤
      eLpNorm (H.indicator (fun _ : α => (2 : ℝ))) (ENNReal.ofReal p) μ := by
    apply eLpNorm_mono_ae
    filter_upwards [hupper] with x hx
    by_cases hh : x∈H
    · rw [indicator_of_mem hh,Real.norm_of_nonneg (le_max_right ((2/τ)*(u x-(1-τ))) 0),
        Real.norm_of_nonneg (by norm_num : (0 : ℝ)≤2)]
      apply max_le
      · have hl : u x-(1-τ)≤τ := by linarith only [hx]
        have hb := mul_le_mul_of_nonneg_left hl ha.le
        have he : (2/τ)*τ=2 := by field_simp [hτ.ne']
        exact hb.trans_eq he
      · norm_num
    · have hl : u x-(1-τ)≤0 := sub_nonpos.mpr (le_of_not_gt hh)
      simp only [indicator_of_notMem hh,max_eq_right (mul_nonpos_of_nonneg_of_nonpos ha.le hl),norm_zero,le_refl]
  rw [eLpNorm_indicator_const₀ hH (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top] at hm
  simpa only [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le,Real.enorm_eq_ofReal (by norm_num : (0 : ℝ)≤2)] using hm

set_option maxHeartbeats 1200000 in
private theorem exists_unit_source_upper_oscillation_drop {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) :
    ∃ δ : ℝ,0<δ ∧ δ<1/2 ∧ ∃ ε₀ : ℝ,0<ε₀ ∧
      ∀ {c : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n},
        WeakPSourceSubsolutionPair p c Ω u g →
        LocalDomain (ball (0 : Space n) (3*((n : ℝ)+1))) Ω →
        (∀ᵐ x ∂volume.restrict (ball (0 : Space n) (3*((n : ℝ)+1))),u x≤1) →
        (1/2 : ℝ)≤((continuousCubeMeasure n) {x | u x≤1/2}).toReal →
        |c|≤ε₀ → ∀ᵐ x ∂volume.restrict (ball (0 : Space n) (1/4 : ℝ)),u x≤1-δ := by
  have hp0 : 0<p := zero_lt_one.trans hp
  obtain ⟨G,hG,hcut⟩ := exists_uniform_scaled_cutoff n
  obtain ⟨ε,hε,hsmall⟩ := exists_uniform_source_small_tail_threshold
    (n:=n) (p:=p) (c:=1) (G:=4*G) hp (by norm_num) (by positivity) hpn
  let η : ℝ := (ε/4)^p/(2 : ℝ)^n
  have hη : 0<η := by dsimp only [η];positivity
  obtain ⟨J,hJ,ε₁,hε₁,hreduce⟩ := exists_unit_cube_source_high_level_reduction (n:=n) hp hη
  let τ : ℝ := (1/2 : ℝ)^(J+1)
  have hτ : 0<τ := by dsimp only [τ];positivity
  let δ : ℝ := τ/2
  have hδ : 0<δ := half_pos hτ
  have hδhalf : δ<1/2 := by
    have ht : τ≤(1/2 : ℝ) := pow_le_of_le_one (by norm_num) (by norm_num) (by omega : J+1≠0)
    dsimp only [δ]
    linarith only [ht]
  let ε₀ : ℝ := min ε₁ ((τ/2)^(p-1))
  have hε₀ : 0<ε₀ := by
    dsimp only [ε₀]
    exact lt_min hε₁ (Real.rpow_pos_of_pos (half_pos hτ) (p-1))
  refine ⟨δ,hδ,hδhalf,ε₀,hε₀,?_⟩
  intro c Ω u g hu hD hu1 hlow hc
  have hmass := hreduce hu hD hu1 hlow (hc.trans (min_le_left _ _))
  let D := ball (0 : Space n) (3*((n : ℝ)+1))
  let B := ball (0 : Space n) (3/4 : ℝ)
  let ν := volume.restrict B
  have hBb : Bornology.IsBounded B := isBounded_ball
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hBb.measure_lt_top.ne
  have hBD : B⊆D := ball_subset_ball (by
    have hn : 0≤(n : ℝ) := Nat.cast_nonneg n
    linarith only [hn])
  have hBΩ : LocalDomain B Ω := by
    refine ⟨isOpen_ball,isBounded_ball,?_⟩
    intro x hx
    have hx' : dist x 0≤(3/4 : ℝ) := by
      have hh := closure_ball_subset_closedBall hx
      exact mem_closedBall.mp hh
    have hxD : x∈D := by
      change dist x 0<3*((n : ℝ)+1)
      have hn : 0≤(n : ℝ) := Nat.cast_nonneg n
      linarith only [hx',hn]
    exact hD.2.2 (subset_closure hxD)
  have huB := hu.2.2.1 B hBΩ
  have hupper : ∀ᵐ x ∂ν,u x≤1 := ae_restrict_of_ae_restrict_of_subset hBD hu1
  let a : ℝ := 2/τ
  have ha : 0<a := div_pos (by norm_num) hτ
  let w : Space n → ℝ := fun x => a*(u x-continuousDGLevel J)
  have hw := hu.affine_positive_actual ha (continuousDGLevel J)
  change WeakPSourceSubsolutionPair p (a^(p-1)*c) Ω w (a • g) at hw
  have hcnew : a^(p-1)*c≤1 := by
    have hccap : |c|≤(τ/2)^(p-1) := hc.trans (min_le_right _ _)
    have hh := mul_le_mul_of_nonneg_left hccap (Real.rpow_nonneg ha.le (p-1))
    have he : a^(p-1)*(τ/2)^(p-1)=1 := by
      rw [←Real.mul_rpow ha.le (half_pos hτ).le]
      have hcanc : a*(τ/2)=1 := by dsimp only [a];field_simp [hτ.ne']
      rw [hcanc,Real.one_rpow]
    exact (mul_le_mul_of_nonneg_left (le_abs_self c) (Real.rpow_nonneg ha.le _)).trans (hh.trans_eq he)
  have hnorm : eLpNorm' (fun x => max (w x) 0) p ν≤ENNReal.ofReal 2*
      (ν {x | continuousDGLevel J<u x})^(1/p) := by
    simpa only [w,a,continuousDGLevel,τ] using
      continuous_normalized_tail_norm_le hp0 hτ huB.2.1.1.aemeasurable hupper
  have hm : (ν {x | continuousDGLevel J<u x}).toReal≤
      (2 : ℝ)^n*((continuousCubeMeasure n) {x | continuousDGLevel J<u x}).toReal := by
    have hνμ := Measure.le_iff'.mp (continuous_small_ball_measure_le_cube n)
      {x | continuousDGLevel J<u x}
    have hf : (2 : ℝ≥0∞)^n*((continuousCubeMeasure n) {x | continuousDGLevel J<u x})≠∞ :=
      ENNReal.mul_ne_top (by finiteness) (measure_ne_top _ _)
    have ht := ENNReal.toReal_mono hf hνμ
    simpa only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_pow,
      ENNReal.toReal_ofNat] using ht
  have hm' : (ν {x | continuousDGLevel J<u x}).toReal<(ε/4)^p := by
    have hmul := mul_lt_mul_of_pos_left hmass (by positivity : (0 : ℝ)<(2 : ℝ)^n)
    have he : (2 : ℝ)^n*η=(ε/4)^p := by dsimp only [η];field_simp
    exact hm.trans_lt (hmul.trans_eq he)
  have hroot : (ν {x | continuousDGLevel J<u x}).toReal^(1/p)<ε/4 := by
    have hh := Real.rpow_lt_rpow ENNReal.toReal_nonneg hm' (one_div_pos.mpr hp0)
    rw [←Real.rpow_mul (by positivity : 0≤ε/4),mul_one_div_cancel hp0.ne',Real.rpow_one] at hh
    exact hh
  have hf : ENNReal.ofReal 2*(ν {x | continuousDGLevel J<u x})^(1/p)≠∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hp0.le) (measure_ne_top _ _))
  have hnormReal := ENNReal.toReal_mono hf hnorm
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by norm_num : (0 : ℝ)≤2),
    ←ENNReal.toReal_rpow] at hnormReal
  have hnormε : (eLpNorm' (fun x => max (w x) 0) p ν).toReal≤ε := by
    linarith only [hnormReal,hroot,hε]
  obtain ⟨χ,hχ,hχ0,hχ1,hχK,_,hχgrad⟩ := hcut 0 (1/4) (by norm_num)
  have hχ' : SmoothTest B χ := by
    simpa only [B,show (3 : ℝ)*(1/4)=3/4 by norm_num] using hχ
  have hgrad (x : Space n) (_ : x∈B) : ‖gradient χ x‖≤4*G := by
    have hh := hχgrad x
    norm_num at hh
    nlinarith only [hh]
  have hresult := hsmall Ω B χ hBΩ hχ' hχ0 hχ1 hgrad (a^(p-1)*c) w (a • g) hcnew hw hnormε
  have ht := ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by norm_num : (1/4 : ℝ)≤3/4)) hresult
  filter_upwards [ht,ae_restrict_mem measurableSet_ball] with x hx hxb
  have hχx : χ x=1 := hχK x (mem_closedBall.mpr (le_of_lt (mem_ball.mp hxb)))
  have hwx := hx hχx
  change (2/τ)*(u x-(1-τ))≤1 at hwx
  have hh := (div_le_iff₀ hτ).mp (by simpa only [div_mul_eq_mul_div] using hwx)
  dsimp only [δ]
  linarith only [hh]

theorem exists_unit_source_oscillation_alternative {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) :
    ∃ δ : ℝ,0<δ ∧ δ<1/2 ∧ ∃ ε₀ : ℝ,0<ε₀ ∧
      ∀ {c : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n},
        WeakPSourcePair p c Ω u g →
        LocalDomain (ball (0 : Space n) (3*((n : ℝ)+1))) Ω →
        (∀ᵐ x ∂volume.restrict (ball (0 : Space n) (3*((n : ℝ)+1))),0≤u x∧u x≤1) →
        |c|≤ε₀ →
        (∀ᵐ x ∂volume.restrict (ball (0 : Space n) (1/4 : ℝ)),u x≤1-δ) ∨
          (∀ᵐ x ∂volume.restrict (ball (0 : Space n) (1/4 : ℝ)),δ≤u x) := by
  obtain ⟨δ,hδ,hδhalf,ε₀,hε₀,hdrop⟩ := exists_unit_source_upper_oscillation_drop hp hpn
  refine ⟨δ,hδ,hδhalf,ε₀,hε₀,?_⟩
  intro c Ω u g hu hD hbound hc
  let μ := continuousCubeMeasure n
  have : IsProbabilityMeasure μ := inferInstance
  by_cases hl : (1/2 : ℝ)≤(μ {x | u x≤1/2}).toReal
  · exact Or.inl (hdrop hu.subsolution hD (hbound.mono (fun _ hx => hx.2)) hl hc)
  · have hcover : {x : Space n | u x≤1/2}∪{x | 1/2≤u x}=Set.univ := by
      ext x
      simp only [mem_union,Set.mem_ofPred_eq,mem_univ,iff_true]
      exact le_total _ _
    have hm := measure_union_le (μ:=μ) {x | u x≤1/2} {x | 1/2≤u x}
    rw [hcover,measure_univ] at hm
    have hmreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _,measure_ne_top μ _⟩) hm
    rw [ENNReal.toReal_one,ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hmreal
    have hhalf : (1/2 : ℝ)≤(μ {x | 1/2≤u x}).toReal := by
      linarith only [hmreal,lt_of_not_ge hl]
    let v : Space n → ℝ := fun x => 1-u x
    have hv : WeakPSourceSubsolutionPair p (-c) Ω v (fun x => -g x) := by
      have hh := (continuous_source_pair_neg hu).subsolution.add_const 1
      have he : (fun x => -u x+1)=v := by funext x;dsimp only [v];ring
      rwa [he] at hh
    have hvbound : ∀ᵐ x ∂volume.restrict (ball (0 : Space n) (3*((n : ℝ)+1))),v x≤1 := by
      filter_upwards [hbound] with x hx
      dsimp only [v]
      linarith only [hx.1]
    have hvhalf : (1/2 : ℝ)≤(μ {x | v x≤1/2}).toReal := by
      have he : {x | v x≤1/2}={x | 1/2≤u x} := by
        ext x
        change (1-u x≤(1/2 : ℝ))↔(1/2 : ℝ)≤u x
        constructor <;> intro h <;> linarith only [h]
      rwa [he]
    have hcv : |-c|≤ε₀ := by simpa only [abs_neg] using hc
    have hout := hdrop hv hD hvbound hvhalf hcv
    right
    filter_upwards [hout] with x hx
    dsimp only [v] at hx
    linarith only [hx]

end BMCompactPDE
#print axioms BMCompactPDE.exists_unit_source_oscillation_alternative
