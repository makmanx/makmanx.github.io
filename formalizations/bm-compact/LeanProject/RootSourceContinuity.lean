import ContinuousSpatialOscillation
import RootSourceFloor
import RootIntervalIteration

/-! Actual selected continuity for the raw constant-source weak PDE, 1<p<n.
The initial bound is derived from the PDE's checked local L-infinity theorem.
Actual spatial oscillation alternatives construct the intervals; the source
floor tends to zero. No oscillation, continuity or classical regularity
conclusion is assumed. This file makes no C1 assertion. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped ENNReal NNReal Topology
namespace BMCompactPDE

private theorem source_continuity_interval_sequences
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hpn : p<(n : ℝ))
    {a : Space n} (ha : a∈Ω) :
    ∃ (r lo hi : ℕ → ℝ),(∀ j,0<r j) ∧
      (∀ j,ball a (r j)⊆Ω) ∧
      (∀ j,∀ᵐ x ∂volume.restrict (ball a (r j)),lo j≤u x ∧ u x≤hi j) ∧
      Tendsto (fun j => hi j-lo j) atTop (𝓝 0) := by
  obtain ⟨δ,hδ,hδhalf,ε,hε,hosc⟩ :=
    exists_source_spatial_oscillation_alternative hu.1 hpn
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hu.2.1 a ha
  let K : ℝ := 3*((n:ℝ)+1)
  have hK3 : 3≤K := by
    dsimp only [K]
    nlinarith [show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n]
  have hK : 0<K := by linarith
  let R0 : ℝ := ρ/(2*K)
  have hR0 : 0<R0 := div_pos hρ (mul_pos (by norm_num) hK)
  have hR0K : R0*K=ρ/2 := by dsimp only [R0];field_simp [hK.ne']
  let t : ℝ := 1/(4*K)
  have ht : 0<t := one_div_pos.mpr (mul_pos (by norm_num) hK)
  have ht1 : t<1 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hK)).mpr
    nlinarith [hK3]
  let r : ℕ → ℝ := fun j => R0*t^j
  let U : ℕ → Set (Space n) := fun j => ball a (r j*K)
  have hr (j : ℕ) : 0<r j := mul_pos hR0 (pow_pos ht j)
  have hrle (j : ℕ) : r j≤R0 := by
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ ht.le ht1.le) hR0.le).trans_eq (mul_one _)
  have hrad (j : ℕ) : r j*K≤ρ/2 :=
    (mul_le_mul_of_nonneg_right (hrle j) hK.le).trans_eq hR0K
  have hnext (j : ℕ) : r (j+1)*K=r j/4 := by
    dsimp only [r,t]
    rw [pow_succ]
    field_simp [hK.ne']
    <;> ring
  have hBΩ : closedBall a (ρ/2)⊆Ω :=
    (closedBall_subset_ball (by linarith only [hρ] : ρ/2<ρ)).trans hball
  have hUB (j : ℕ) : U j⊆closedBall a (ρ/2) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (hrad j))
  have hD (j : ℕ) : LocalDomain (U j) Ω := by
    refine ⟨isOpen_ball,isBounded_ball,?_⟩
    exact (closure_ball_subset_closedBall.trans
      (closedBall_subset_closedBall (hrad j))).trans hBΩ
  have hnested (j : ℕ) : U (j+1)⊆U j := by
    change ball a (r (j+1)*K)⊆ball a (r j*K)
    rw [hnext]
    apply ball_subset_ball
    nlinarith [hr j,hK3]
  have hLp := hu.memLp_top_compact hpn (isCompact_closedBall a (ρ/2)) hBΩ
  have hfinite : eLpNormEssSup u (volume.restrict (closedBall a (ρ/2)))<∞ := by
    simpa only [eLpNorm_exponent_top] using hLp.2
  obtain ⟨C,hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hfinite
  let B : ℝ := max (C:ℝ) 1
  have hB1 : 1≤B := le_max_right _ _
  have hboundB : ∀ᵐ x ∂volume.restrict (closedBall a (ρ/2)),‖u x‖≤B := by
    filter_upwards [hC] with x hx
    have hh : ‖u x‖≤(C:ℝ) := by exact_mod_cast hx
    exact hh.trans (le_max_left _ _)
  have hinit : ∀ᵐ x ∂volume.restrict (U 0),-B≤u x ∧ u x≤B := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (hUB 0) hboundB] with x hx
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hx)
  let q : ℝ := 1-δ
  have hq0 : 0≤q := by dsimp only [q];linarith
  have hq1 : q<1 := by dsimp only [q];linarith
  let F : ℕ → ℝ := fun j => (|c|/ε)^(1/(p-1))*(r j)^(p/(p-1))
  have hF : Tendsto F atTop (𝓝 0) :=
    BMCompactRegularity.tendsto_geometric_source_floor hu.1 hR0 ht.le ht1 ε c
  have hstep (j : ℕ) (lo hi : ℝ) (hle : lo≤hi)
      (hae : ∀ᵐ x ∂volume.restrict (U j),lo≤u x ∧ u x≤hi) :
      ∃ lo' hi' : ℝ,lo'≤hi' ∧
        (∀ᵐ x ∂volume.restrict (U (j+1)),lo'≤u x ∧ u x≤hi') ∧
        hi'-lo'≤max (q*(hi-lo)) (F j) := by
    have hinner := ae_restrict_of_ae_restrict_of_subset (hnested j) hae
    rcases lt_or_eq_of_le hle with hlt|heq
    · by_cases hsmall : (r j)^p*|c|≤ε*(hi-lo)^(p-1)
      · have halt := hosc hu a (r j) lo hi (hr j) hlt (hD j) hae hsmall
        have hUeq : U (j+1)=ball a (r j/4) := congrArg (ball a) (hnext j)
        have hδle : δ*(hi-lo)≤hi-lo := by
          have hh := mul_le_mul_of_nonneg_right
            (show δ≤1 by linarith only [hδhalf]) (sub_nonneg.mpr hle)
          simpa only [one_mul] using hh
        rcases halt with hup|hlo
        · refine ⟨lo,hi-δ*(hi-lo),by linarith only [hδle],?_,?_⟩
          · have hup' : ∀ᵐ x ∂volume.restrict (U (j+1)),u x≤hi-δ*(hi-lo) := by
              simpa only [hUeq] using hup
            filter_upwards [hinner,hup'] with x hx hy using ⟨hx.1,hy⟩
          · have he : hi-δ*(hi-lo)-lo=q*(hi-lo) := by dsimp only [q];ring
            rw [he]
            exact le_max_left _ _
        · refine ⟨lo+δ*(hi-lo),hi,by linarith only [hδle],?_,?_⟩
          · have hlo' : ∀ᵐ x ∂volume.restrict (U (j+1)),lo+δ*(hi-lo)≤u x := by
              simpa only [hUeq] using hlo
            filter_upwards [hinner,hlo'] with x hx hy using ⟨hy,hx.2⟩
          · have he : hi-(lo+δ*(hi-lo))=q*(hi-lo) := by dsimp only [q];ring
            rw [he]
            exact le_max_left _ _
      · refine ⟨lo,hi,hle,hinner,?_⟩
        have hf := BMCompactRegularity.source_floor_of_not_small hu.1 (hr j) hε
          (sub_nonneg.mpr hle) hsmall
        exact hf.trans (le_max_right _ _)
    · refine ⟨lo,hi,hle,hinner,?_⟩
      simpa only [heq,sub_self,mul_zero] using (le_max_left (0:ℝ) (F j))
  obtain ⟨lo,hi,-,hae,hlim⟩ := BMCompactRegularity.exists_decaying_ae_interval_sequence
    volume u U hq0 hq1 F hF (-B) B (by linarith only [hB1]) hinit hstep
  exact ⟨fun j => r j*K,lo,hi,fun j => mul_pos (hr j) hK,
    fun j => subset_closure.trans (hD j).2.2,hae,hlim⟩

theorem WeakPSourcePair.vanishingEssentialOscillation_actual
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hpn : p<(n : ℝ)) :
    BMCompactRepresentative.VanishingEssentialOscillation volume u Ω := by
  apply BMCompactRepresentative.vanishingEssentialOscillation_of_interval_sequences volume
  exact fun a ha => source_continuity_interval_sequences hu hpn ha

theorem WeakPSourcePair.exists_unique_continuousRepresentative_actual
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hpn : p<(n : ℝ)) :
    ∃ v : Space n → ℝ,ContinuousOn v Ω ∧ u =ᵐ[volume.restrict Ω] v ∧
      ∀ w : Space n → ℝ,ContinuousOn w Ω → u =ᵐ[volume.restrict Ω] w → EqOn v w Ω := by
  exact BMCompactRepresentative.exists_unique_continuousRepresentative volume hu.2.1
    (hu.vanishingEssentialOscillation_actual hpn)

theorem WeakPSourcePair.exists_continuous_weak_representative
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (hpn : p<(n : ℝ)) :
    ∃ v : Space n → ℝ,ContinuousOn v Ω ∧ u =ᵐ[volume.restrict Ω] v ∧
      WeakPSourcePair p c Ω v g := by
  obtain ⟨v,hv,huv,-⟩ := hu.exists_unique_continuousRepresentative_actual hpn
  exact ⟨v,hv,huv,hu.1,hu.2.1,
    hu.2.2.1.congr_ae huv EventuallyEq.rfl,hu.2.2.2⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.vanishingEssentialOscillation_actual
#print axioms BMCompactPDE.WeakPSourcePair.exists_unique_continuousRepresentative_actual
#print axioms BMCompactPDE.WeakPSourcePair.exists_continuous_weak_representative
