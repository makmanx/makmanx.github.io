import ContinuousDeGiorgiBatch
import Mathlib.Data.ENNReal.BigOperators
import RootFiniteBands

/-! Exact source-body batch: actual raw level sets, fixed unit geometry, disjoint band measures,
and actual normalized cube source-PDE energy. See adjacent provenance. -/

noncomputable section ContinuousBody_ContinuousActualLevels

/-! Actual raw weak level sets. Null measurability comes from the Sobolev
graph, not from a pointwise measurable/continuous representative premise. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
namespace BMCompactPDE

theorem continuous_ball_one_subset_cube (n : ℕ) :
    Metric.ball (0 : Space n) 1⊆continuousUnitCube n := by
  intro x hx
  change ∀ i∈(Set.univ : Set (Fin n)),-1<x i∧x i<1
  intro i _
  have hn : |x i|≤‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hnx : ‖x‖<1 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  exact abs_lt.mp (hn.trans_lt hnx)

theorem continuous_cube_subset_ball (n : ℕ) :
    continuousUnitCube n⊆Metric.ball (0 : Space n) ((n : ℝ)+1) := by
  intro x hx
  have hx' : ∀ i : Fin n,-1<x i∧x i<1 := by
    simpa only [continuousUnitCube,mem_preimage,Set.mem_pi,mem_univ,true_implies,mem_Ioo] using hx
  have hsq : ‖x‖^2≤(n : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ i : Fin n,(x i)^2)≤∑ _i : Fin n,(1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hx' i
        nlinarith [sq_nonneg (x i)]
      _=(n : ℝ) := by simp
  have hn : 0≤(n : ℝ) := Nat.cast_nonneg n
  have hnorm : ‖x‖<(n : ℝ)+1 := by nlinarith [norm_nonneg x,sq_nonneg (n : ℝ)]
  simpa only [Metric.mem_ball,dist_zero_right] using hnorm

theorem SobolevPair.cube_actual_level_band_holder {n : ℕ} {p : ℝ}
    {Ω K : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p Ω u g) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hK : IsCompact K) (hcube : continuousUnitCube n⊆K) (hKΩ : K⊆Ω)
    {k l : ℝ} (hkl : k≤l) :
    (l-k)*((continuousCubeMeasure n) {x | u x≤k}).toReal*
      ((continuousCubeMeasure n) {x | l≤u x}).toReal ≤
      (Real.pi/2)*(∫ x in {x | k<u x∧u x≤l},‖g x‖^p ∂continuousCubeMeasure n)^(1/p)*
        ((continuousCubeMeasure n) {x | k<u x∧u x≤l}).toReal^(1-1/p) := by
  let μ := continuousCubeMeasure n
  have hae : ∀ᵐ x ∂μ,x∈Ω :=
    (continuousCubeMeasure_ae_mem n).mono (fun _ hx => hKΩ (hcube hx))
  have hμΩ : μ≤volume.restrict Ω := by
    have hm := Measure.restrict_mono_measure (continuousCubeMeasure_le_volume n) Ω
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at hm
  have hum : AEMeasurable u μ := (hu.2.1.mono_measure hμΩ).1.aemeasurable
  have hZ : NullMeasurableSet {x | u x≤k} μ := nullMeasurableSet_le hum aemeasurable_const
  have hH : NullMeasurableSet {x | l≤u x} μ := nullMeasurableSet_le aemeasurable_const hum
  have hz : ∀ᵐ x ∂μ.restrict (toMeasurable μ {x | u x≤k}),u x≤k :=
    (ae_restrict_congr_set hZ.toMeasurable_ae_eq).mpr (ae_restrict_mem₀ hZ)
  have hh : ∀ᵐ x ∂μ.restrict (toMeasurable μ {x | l≤u x}),l≤u x :=
    (ae_restrict_congr_set hH.toMeasurable_ae_eq).mpr (ae_restrict_mem₀ hH)
  have hb := hu.cube_level_band_holder hΩ hΩb hK hcube hKΩ hkl
    (measurableSet_toMeasurable _ _) (measurableSet_toMeasurable _ _) hz hh
  simpa only [μ,measure_toMeasurable] using hb

/-- The genuine half-open bands of an a.e. measurable function have total
probability at most one. This supplies the finite-band scalar lemma with
actual measure data rather than an assumed summability/oscillation class. -/
theorem continuous_level_band_sum_le_one {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {u : α → ℝ}
    (hu : AEMeasurable u μ) {k : ℕ → ℝ} (hk : Monotone k) (J : ℕ) :
    (∑ j : Fin J,(μ {x | k (j : ℕ)<u x∧u x≤k ((j : ℕ)+1)}).toReal)≤1 := by
  classical
  let B : Fin J → Set α := fun j => {x | k (j : ℕ)<u x∧u x≤k ((j : ℕ)+1)}
  have hB (j : Fin J) : NullMeasurableSet (B j) μ :=
    (nullMeasurableSet_lt aemeasurable_const hu).inter
      (nullMeasurableSet_le hu aemeasurable_const)
  have hd : Pairwise (fun i j : Fin J => Disjoint (B i) (B j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases lt_or_gt_of_ne hij with hijlt|hjilt
    · have hb : k ((i : ℕ)+1)≤k (j : ℕ) := hk (Nat.succ_le_of_lt hijlt)
      exact not_lt_of_ge (hx.2.trans hb) hy.1
    · have hb : k ((j : ℕ)+1)≤k (i : ℕ) := hk (Nat.succ_le_of_lt hjilt)
      exact not_lt_of_ge (hy.2.trans hb) hx.1
  have hs : (∑ j : Fin J,μ (B j))≤1 := by
    simpa using
      (sum_measure_le_measure_univ (s:=Finset.univ) (fun j _ => hB j)
        (fun i _ j _ hij => (hd hij).aedisjoint))
  have ht := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞)≠∞) hs
  rw [ENNReal.toReal_sum (fun j _ => measure_ne_top μ (B j)),ENNReal.toReal_one] at ht
  exact ht

end BMCompactPDE

end ContinuousBody_ContinuousActualLevels

noncomputable section ContinuousBody_ContinuousCubeEnergy

/-! Actual source energy on the normalized cube. These estimates combine the
actual weak PDE, compact cutoff energy and actual cube-volume geometry. -/
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal BigOperators
namespace BMCompactPDE

theorem exists_unit_cube_source_band_energy (n : ℕ) :
    ∃ G : ℝ,0<G ∧ ∀ {p c : ℝ} {Ω : Set (Space n)}
      {u : Space n → ℝ} {g : Space n → Space n},
      WeakPSourceSubsolutionPair p c Ω u g →
      LocalDomain (ball (0 : Space n) (3*((n : ℝ)+1))) Ω →
      ∀ (M : ℕ),p≤(M : ℝ) → ∀ k l : ℝ,
      (∫ x in {x | k<u x∧u x≤l},‖g x‖^p ∂continuousCubeMeasure n) ≤
        (M : ℝ)^p*(G/((n : ℝ)+1))^p*
          (∫ x in ball (0 : Space n) (3*((n : ℝ)+1)),(max (u x-k) 0)^p)+
        p*|c| *(∫ x in ball (0 : Space n) (3*((n : ℝ)+1)),max (u x-k) 0) := by
  obtain ⟨G,hG,hEnergy⟩ := exists_uniform_source_level_energy n
  refine ⟨G,hG,?_⟩
  intro p c Ω u g hu hD M hm k l
  let r : ℝ := (n : ℝ)+1
  let I := ball (0 : Space n) r
  let D := ball (0 : Space n) (3*r)
  let μ := continuousCubeMeasure n
  let ν := volume.restrict I
  have hr : 0<r := by dsimp only [r];positivity
  have hID : I⊆D := ball_subset_ball (by linarith only [hr])
  have hS := hu.2.2.1 D hD
  have hνD : ν≤volume.restrict D := Measure.restrict_mono_set volume hID
  have hUν := hS.2.1.mono_measure hνD
  have hGν := hS.2.2.1.mono_measure hνD
  have hμν : μ≤ν := by
    have hae : ∀ᵐ x ∂μ,x∈I := (continuousCubeMeasure_ae_mem n).mono
      (fun _ hx => continuous_cube_subset_ball n hx)
    have h := Measure.restrict_mono_measure (continuousCubeMeasure_le_volume n) I
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at h
  have hUμ := hUν.mono_measure hμν
  have hGμ := hGν.mono_measure hμν
  have hPIν := integrable_norm_rpow_of_memLp hu.1 hGν
  have hPIμ := integrable_norm_rpow_of_memLp hu.1 hGμ
  let F : Space n → ℝ := fun x => if k<u x then ‖g x‖^p else 0
  let B := {x | k<u x∧u x≤l}
  have hB : NullMeasurableSet B μ :=
    (nullMeasurableSet_lt aemeasurable_const hUμ.1.aemeasurable).inter
      (nullMeasurableSet_le hUμ.1.aemeasurable aemeasurable_const)
  have hFIν : Integrable F ν := hPIν.indicator₀
    (nullMeasurableSet_lt aemeasurable_const hUν.1.aemeasurable)
  have hFIμ : Integrable F μ := hFIν.mono_measure hμν
  have hF0 (x : Space n) : 0≤F x := by dsimp only [F];split_ifs <;> positivity
  have hfirst : (∫ x in B,‖g x‖^p ∂μ)≤∫ x,F x ∂μ := by
    rw [←integral_indicator₀ hB]
    apply integral_mono_ae (hPIμ.indicator₀ hB) hFIμ
    exact Eventually.of_forall (fun x => by
      by_cases hx : x∈B
      · rw [indicator_of_mem hx]
        simp only [F,if_pos hx.1,le_refl]
      · rw [indicator_of_notMem hx]
        exact hF0 x)
  have hsecond : (∫ x,F x ∂μ)≤∫ x,F x ∂ν :=
    integral_mono_measure hμν (Eventually.of_forall hF0) hFIν
  exact (hfirst.trans hsecond).trans (hEnergy hu 0 r hr hD M hm k)

end BMCompactPDE

end ContinuousBody_ContinuousCubeEnergy

noncomputable section ContinuousBody_ContinuousSecondDeGiorgi

/-! The finite-level De Giorgi measure reduction from actual source energy.
The normalized bound is intermediate iteration data; no continuity or
oscillation-decay class is assumed, and no such regularity is concluded here.
-/
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal BigOperators
namespace BMCompactPDE

def continuousDGLevel (j : ℕ) : ℝ := 1-(1/2 : ℝ)^(j+1)

private theorem continuousDGLevel_monotone : Monotone continuousDGLevel := by
  intro i j hij
  exact sub_le_sub_left (pow_le_pow_of_le_one (by norm_num : (0 : ℝ)≤1/2)
    (by norm_num : (1/2 : ℝ)≤1) (Nat.add_le_add_right hij 1)) 1

private theorem continuous_tail_integrals_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {u : α → ℝ} {p k τ : ℝ}
    (hp : 0<p) (_hτ : 0≤τ) (hu : AEStronglyMeasurable u μ)
    (hbound : ∀ᵐ x ∂μ,max (u x-k) 0≤τ) :
    (∫ x,max (u x-k) 0 ∂μ)≤μ.real Set.univ*τ ∧
      (∫ x,(max (u x-k) 0)^p ∂μ)≤μ.real Set.univ*τ^p := by
  have hm : AEStronglyMeasurable (fun x => max (u x-k) 0) μ :=
    ((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable hu
  have hn : ∀ᵐ x ∂μ,0≤max (u x-k) 0 := Eventually.of_forall (fun _ => le_max_right _ _)
  have hi : Integrable (fun x => max (u x-k) 0) μ :=
    (integrable_const τ).mono_nonneg hm hn hbound
  have hpmeas : AEStronglyMeasurable (fun x => (max (u x-k) 0)^p) μ :=
    (continuous_id.rpow_const (fun _ => Or.inr hp.le)).comp_aestronglyMeasurable hm
  have hpnon : ∀ᵐ x ∂μ,0≤(max (u x-k) 0)^p :=
    Eventually.of_forall (fun _ => Real.rpow_nonneg (le_max_right _ _) _)
  have hpbound : (fun x => (max (u x-k) 0)^p)≤ᵐ[μ](fun _ => τ^p) := by
    filter_upwards [hbound] with x hx
    exact Real.rpow_le_rpow (le_max_right _ _) hx hp.le
  have hpi : Integrable (fun x => (max (u x-k) 0)^p) μ :=
    (integrable_const (τ^p)).mono_nonneg hpmeas hpnon hpbound
  constructor
  · simpa only [integral_const,smul_eq_mul] using integral_mono_ae hi (integrable_const τ) hbound
  · simpa only [integral_const,smul_eq_mul] using
      integral_mono_ae hpi (integrable_const (τ^p)) hpbound

set_option maxHeartbeats 1200000 in
theorem exists_unit_cube_source_high_level_reduction {n : ℕ} {p η : ℝ}
    (hp : 1<p) (hη : 0<η) :
    ∃ J : ℕ,0<J ∧ ∃ ε₀ : ℝ,0<ε₀ ∧
      ∀ {c : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n},
        WeakPSourceSubsolutionPair p c Ω u g →
        LocalDomain (ball (0 : Space n) (3*((n : ℝ)+1))) Ω →
        (∀ᵐ x ∂volume.restrict (ball (0 : Space n) (3*((n : ℝ)+1))),u x≤1) →
        (1/2 : ℝ)≤((continuousCubeMeasure n) {x | u x≤1/2}).toReal →
        |c|≤ε₀ → ((continuousCubeMeasure n) {x | continuousDGLevel J<u x}).toReal<η := by
  have hp0 : 0<p := zero_lt_one.trans hp
  have hθ : 0<1-1/p := by
    have hi : 1/p<1 := (div_lt_iff₀ hp0).mpr (by simpa only [one_mul] using hp)
    linarith
  let r : ℝ := (n : ℝ)+1
  let D := ball (0 : Space n) (3*r)
  let V : ℝ := (volume D).toReal
  have hV : 0≤V := ENNReal.toReal_nonneg
  have hr : 0<r := by dsimp only [r];positivity
  obtain ⟨G,hG,hEnergy⟩ := exists_unit_cube_source_band_energy n
  obtain ⟨M,hM⟩ := exists_nat_gt p
  have hm : p≤(M : ℝ) := hM.le
  let a : ℝ := (M : ℝ)^p*(G/r)^p
  let E : ℝ := (a+p)*V
  let C : ℝ := 1+E
  have ha : 0≤a := by dsimp only [a];positivity
  have hE : 0≤E := mul_nonneg (add_nonneg ha hp0.le) hV
  have hC : 0<C := by dsimp only [C];linarith
  let A : ℝ := 1+4*(Real.pi/2)*C^(1/p)
  have hA : 0<A := by dsimp only [A];positivity
  obtain ⟨J,hJ,hJsmall⟩ := BMCompactRegularity.finite_band_smallness_index hθ hA hη 1
  let τ : ℕ → ℝ := fun j => (1/2 : ℝ)^(j+1)
  have hτ (j : ℕ) : 0<τ j := by dsimp only [τ];positivity
  let ε₀ : ℝ := (τ J/2)^(p-1)
  have hε₀ : 0<ε₀ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨J,hJ,ε₀,hε₀,?_⟩
  intro c Ω u g hu hD hu1 hlow hc
  let μ := continuousCubeMeasure n
  have : IsProbabilityMeasure μ := inferInstance
  let ν := volume.restrict D
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hD.2.1.measure_lt_top.ne
  have hS := hu.2.2.1 D hD
  have hμν : μ≤ν := by
    have hae : ∀ᵐ x ∂μ,x∈D := (continuousCubeMeasure_ae_mem n).mono (fun x hx => by
      have hx' := continuous_cube_subset_ball n hx
      exact (ball_subset_ball (by linarith only [hr] : r≤3*r)) hx')
    have hh := Measure.restrict_mono_measure (continuousCubeMeasure_le_volume n) D
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at hh
  have hum : AEMeasurable u μ := (hS.2.1.mono_measure hμν).1.aemeasurable
  let b : Fin J → ℝ := fun j => (μ {x | continuousDGLevel (j : ℕ)<u x∧
    u x≤continuousDGLevel ((j : ℕ)+1)}).toReal
  let Y : ℝ := (μ {x | continuousDGLevel J<u x}).toReal
  have hb (j : Fin J) : 0≤b j := ENNReal.toReal_nonneg
  have hbsum : (∑ j,b j)≤1 :=
    continuous_level_band_sum_le_one hum continuousDGLevel_monotone J
  apply hJsmall Y b hb hbsum
  intro j
  let k := continuousDGLevel (j : ℕ)
  let l := continuousDGLevel ((j : ℕ)+1)
  have hjJ : (j : ℕ)+1≤J := Nat.succ_le_of_lt j.isLt
  have hkbase : (1/2 : ℝ)≤k := by
    have hh := continuousDGLevel_monotone (Nat.zero_le (j : ℕ))
    norm_num [continuousDGLevel] at hh ⊢
    exact hh
  have hkl : k≤l := continuousDGLevel_monotone (Nat.le_succ _)
  have hlJ : l≤continuousDGLevel J := continuousDGLevel_monotone hjJ
  have hdiff : l-k=τ j/2 := by
    dsimp only [l,k,continuousDGLevel,τ]
    simp only [pow_succ]
    ring
  have hτJ : τ J/2≤τ j := by
    have hh : τ J≤τ j := pow_le_pow_of_le_one (by norm_num : (0 : ℝ)≤1/2)
      (by norm_num : (1/2 : ℝ)≤1) (Nat.add_le_add_right (Nat.le_of_lt j.isLt) 1)
    linarith only [hh,hτ J]
  have hcτ : |c|≤(τ j)^(p-1) := hc.trans
    (Real.rpow_le_rpow (by positivity : 0≤τ J/2) hτJ (sub_pos.mpr hp).le)
  have htail : ∀ᵐ x ∂ν,max (u x-k) 0≤τ j := by
    filter_upwards [hu1] with x hx
    apply max_le
    · dsimp only [k,continuousDGLevel,τ]
      linarith only [hx]
    · exact (hτ j).le
  obtain ⟨hTI,hPI⟩ := continuous_tail_integrals_bound hp0 (hτ j).le hS.2.1.1 htail
  have hTI' : (∫ x in D,max (u x-k) 0)≤V*τ j := by
    simpa only [ν,measureReal_def,Measure.restrict_apply_univ,V] using hTI
  have hPI' : (∫ x in D,(max (u x-k) 0)^p)≤V*(τ j)^p := by
    simpa only [ν,measureReal_def,Measure.restrict_apply_univ,V] using hPI
  have hcτmul : |c| *τ j≤(τ j)^p := by
    have hh := mul_le_mul_of_nonneg_right hcτ (hτ j).le
    have he : (τ j)^(p-1)*τ j=(τ j)^p := by
      calc
        (τ j)^(p-1)*τ j=(τ j)^(p-1)*(τ j)^1 := by rw [Real.rpow_one]
        _=(τ j)^((p-1)+1) := (Real.rpow_add (hτ j) _ _).symm
        _=(τ j)^p := by congr 1;ring
    exact hh.trans_eq he
  have hEn : (∫ x in {x | k<u x∧u x≤l},‖g x‖^p ∂μ)≤C*(τ j)^p := by
    have he := hEnergy hu hD M hm k l
    have ht := add_le_add (mul_le_mul_of_nonneg_left hPI' ha)
      (mul_le_mul_of_nonneg_left hTI' (mul_nonneg hp0.le (abs_nonneg c)))
    have hsrc : p*|c| *(V*τ j)≤p*V*(τ j)^p := by
      calc
        p*|c| *(V*τ j)=p*V*(|c| *τ j) := by ring
        _≤p*V*(τ j)^p := mul_le_mul_of_nonneg_left hcτmul (mul_nonneg hp0.le hV)
    have he' : (∫ x in {x | k<u x∧u x≤l},‖g x‖^p ∂μ)≤E*(τ j)^p := by
      calc
        _≤a*(V*(τ j)^p)+p*|c| *(V*τ j) := he.trans ht
        _≤a*(V*(τ j)^p)+p*V*(τ j)^p := add_le_add le_rfl hsrc
        _=E*(τ j)^p := by dsimp only [E];ring
    exact he'.trans (mul_le_mul_of_nonneg_right (by dsimp only [C];linarith : E≤C)
      (Real.rpow_nonneg (hτ j).le _))
  have hEn0 : 0≤∫ x in {x | k<u x∧u x≤l},‖g x‖^p ∂μ :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hroot : (∫ x in {x | k<u x∧u x≤l},‖g x‖^p ∂μ)^(1/p)≤C^(1/p)*τ j := by
    have hh := Real.rpow_le_rpow hEn0 hEn (one_div_nonneg.mpr hp0.le)
    rw [Real.mul_rpow hC.le (Real.rpow_nonneg (hτ j).le _),
      ←Real.rpow_mul (hτ j).le,mul_one_div_cancel hp0.ne',Real.rpow_one] at hh
    exact hh
  have hKD : closedBall (0 : Space n) r⊆D := by
    intro x hx
    exact lt_of_le_of_lt (mem_closedBall.mp hx) (by linarith only [hr])
  have hcubeK : continuousUnitCube n⊆closedBall (0 : Space n) r :=
    (continuous_cube_subset_ball n).trans ball_subset_closedBall
  have hholder := hS.cube_actual_level_band_holder isOpen_ball isBounded_ball
    (isCompact_closedBall (0 : Space n) r) hcubeK hKD hkl
  have hZ : (1/2 : ℝ)≤(μ {x | u x≤k}).toReal := hlow.trans
    (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (fun _ hx => hx.trans hkbase)))
  have hH : Y≤(μ {x | l≤u x}).toReal := ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono (fun _ hx => hlJ.trans (le_of_lt hx)))
  have hZ0 : 0≤(μ {x | u x≤k}).toReal := ENNReal.toReal_nonneg
  have hY0 : 0≤Y := ENNReal.toReal_nonneg
  have hmass := mul_le_mul hZ hH hY0 hZ0
  have hmass' := mul_le_mul_of_nonneg_left hmass (div_nonneg (hτ j).le (by norm_num : (0 : ℝ)≤2))
  have hright := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ)≤Real.pi/2))
    (Real.rpow_nonneg (hb j) (1-1/p))
  rw [hdiff] at hholder
  change (τ j/2)*(μ {x | u x≤k}).toReal*(μ {x | l≤u x}).toReal≤
    (Real.pi/2)*(∫ x in {x | k<u x∧u x≤l},‖g x‖^p ∂μ)^(1/p)*(b j)^(1-1/p) at hholder
  have hmass'' : (τ j/4)*Y≤(τ j/2)*(μ {x | u x≤k}).toReal*(μ {x | l≤u x}).toReal := by
    calc
      (τ j/4)*Y=(τ j/2)*((1/2)*Y) := by ring
      _≤(τ j/2)*((μ {x | u x≤k}).toReal*(μ {x | l≤u x}).toReal) := hmass'
      _=(τ j/2)*(μ {x | u x≤k}).toReal*(μ {x | l≤u x}).toReal := by ring
  have hcombined := hmass''.trans (hholder.trans hright)
  have hcancel : τ j*Y≤τ j*(4*(Real.pi/2)*C^(1/p)*(b j)^(1-1/p)) := by
    calc
      τ j*Y=4*((τ j/4)*Y) := by ring
      _≤4*((Real.pi/2)*(C^(1/p)*τ j)*(b j)^(1-1/p)) :=
        mul_le_mul_of_nonneg_left hcombined (by norm_num : (0 : ℝ)≤4)
      _=τ j*(4*(Real.pi/2)*C^(1/p)*(b j)^(1-1/p)) := by ring
  have hy := le_of_mul_le_mul_left hcancel (hτ j)
  exact hy.trans (mul_le_mul_of_nonneg_right (by dsimp only [A];linarith :
      4*(Real.pi/2)*C^(1/p)≤A) (Real.rpow_nonneg (hb j) _))

end BMCompactPDE

end ContinuousBody_ContinuousSecondDeGiorgi

#print axioms BMCompactPDE.SobolevPair.cube_actual_level_band_holder
#print axioms BMCompactPDE.continuous_level_band_sum_le_one
#print axioms BMCompactPDE.continuous_ball_one_subset_cube
#print axioms BMCompactPDE.continuous_cube_subset_ball
#print axioms BMCompactPDE.exists_unit_cube_source_band_energy
#print axioms BMCompactPDE.exists_unit_cube_source_high_level_reduction
