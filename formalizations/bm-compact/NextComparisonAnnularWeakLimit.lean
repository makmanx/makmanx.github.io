import NextComparisonLpGradientCauchy
import NextComparisonRawScalarLp
import UpstreamGreenExteriorExhaustion
import UpstreamGreenLocalLpLimit
import UpstreamGreenLocalPDEClosure
import UpstreamCriticalContinuity
import NextRootContinuousOrder

/-! A genuine annular weak-solution family with a continuous local scalar
majorant and smaller-ball antitonicity has a selected continuous weak limit.
The scalar pointwise limit, strong scalar Lp convergence, local gradient
Cauchy property, ONE raw gradient, strong gradient limits and weak PDE are
all derived. Raw pointwise convergence is asserted only for the raw limit;
its selected C0 representative is identified almost everywhere. No local
uniform convergence or pointwise equality of those representatives is claimed.
The annular family, common scalar majorant and order are explicit generic
inputs; actual critical annular existence is a separate composition. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem green_radial_eventual_antitone_pointwise_limit
    {n : ℕ} {R : ℕ → ℝ} (hRmono : Monotone R) (hRlim : Tendsto R atTop atTop)
    {G : ℕ → Space n → ℝ} (hG0 : ∀ j x,0≤G j x)
    (horder : ∀ j k,j≤k → ∀ x∈ball 0 (R j),G k x≤G j x) :
    ∃ v : Space n → ℝ,∀ x,Tendsto (fun j=>G j x) atTop (𝓝 (v x)) := by
  classical
  have hex (x : Space n) : ∃ l : ℝ,Tendsto (fun j=>G j x) atTop (𝓝 l) := by
    obtain ⟨J,hJ⟩ := (hRlim.eventually (eventually_gt_atTop ‖x‖)).exists
    have hxJ : x∈ball (0 : Space n) (R J) := by simpa only [mem_ball,dist_zero_right] using hJ
    have hanti : Antitone (fun j : ℕ=>G (j+J) x) := by
      intro j k hjk
      apply horder (j+J) (k+J) (Nat.add_le_add_right hjk J) x
      exact ball_subset_ball (hRmono (by omega : J≤j+J)) hxJ
    have hbelow : BddBelow (range (fun j : ℕ=>G (j+J) x)) := by
      refine ⟨0,?_⟩
      rintro _ ⟨j,rfl⟩
      exact hG0 (j+J) x
    exact ⟨_,(tendsto_add_atTop_iff_nat J).mp (tendsto_atTop_ciInf hanti hbelow)⟩
  choose v hv using hex
  exact ⟨v,hv⟩

private theorem green_cauchySeq_of_nat_shift {X : Type*} [PseudoMetricSpace X]
    {f : ℕ → X} (J : ℕ) (hc : CauchySeq (fun j=>f (j+J))) : CauchySeq f := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc ε hε
  refine ⟨N+J,?_⟩
  intro j hj k hk
  have hjN : N≤j-J := by omega
  have hkN : N≤k-J := by omega
  have hjJ : j-J+J=j := Nat.sub_add_cancel (by omega : J≤j)
  have hkJ : k-J+J=k := Nat.sub_add_cancel (by omega : J≤k)
  simpa only [hjJ,hkJ] using hN (j-J) hjN (k-J) hkN

set_option maxHeartbeats 2200000 in
theorem exists_selected_weak_limit_of_bounded_annular_family
    {n : ℕ} {p : ℝ} (hn : 2≤n) (hp2 : 2≤p)
    {K : Set (Space n)} (hK : IsCompact K) (hKne : K.Nonempty)
    {R : ℕ → ℝ} (hRmono : Monotone R) (hRlim : Tendsto R atTop atTop)
    {G : ℕ → Space n → ℝ} {Γ : ℕ → Space n → Space n}
    (hGc : ∀ j,Continuous (G j)) (hGK : ∀ j x,x∈K → G j x=0)
    (hSob : ∀ j B,Bornology.IsBounded B → SobolevPair p B (G j) (Γ j))
    (hH : ∀ j,WeakPHarmonicPair p (ball 0 (R j)\K) (G j) (Γ j))
    {F : Space n → ℝ} (hFc : Continuous F)
    (hB : ∀ j x,0≤G j x ∧ G j x≤F x)
    (horder : ∀ j k,j≤k → ∀ x∈ball 0 (R j),G k x≤G j x) :
    ∃ v w : Space n → ℝ,∃ g : Space n → Space n,
      (∀ x,Tendsto (fun j=>G j x) atTop (𝓝 (v x))) ∧
      (∀ x∈K,v x=0) ∧ (∀ x,0≤v x ∧ v x≤F x) ∧
      ContinuousOn w Kᶜ ∧ v =ᵐ[volume.restrict Kᶜ] w ∧
      (∀ x∈K,w x=0) ∧ (∀ x,0≤w x ∧ w x≤F x) ∧
      WeakPHarmonicPair p Kᶜ w g ∧
      ∀ D : Set (Space n),LocalDomain D Kᶜ →
        MemLp w (ENNReal.ofReal p) (volume.restrict D) ∧
        MemLp g (ENNReal.ofReal p) (volume.restrict D) ∧
        Tendsto (fun j=>eLpNorm (G j-w) (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0) ∧
        Tendsto (fun j=>eLpNorm (Γ j-g) (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0) := by
  classical
  obtain ⟨v,hpoint⟩ := green_radial_eventual_antitone_pointwise_limit hRmono hRlim
    (fun j x=>(hB j x).1) horder
  have hvK (x : Space n) (hx : x∈K) : v x=0 := by
    apply tendsto_nhds_unique (hpoint x)
    simpa only [hGK _ x hx] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0 : ℝ)) atTop (𝓝 0))
  have hvB (x : Space n) : 0≤v x ∧ v x≤F x :=
    ⟨ge_of_tendsto (hpoint x) (Eventually.of_forall (fun j=>(hB j x).1)),
      le_of_tendsto (hpoint x) (Eventually.of_forall (fun j=>(hB j x).2))⟩
  have hp : 1<p := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) hp2
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hΩ : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hscalarBound (E : Set (Space n)) (hEb : Bornology.IsBounded E) :
      ∃ B : ℝ,0<B ∧ ∀ j x,x∈E → |G j x|≤B := by
    have hi : IsCompact (F '' closure E) := hEb.isCompact_closure.image hFc
    obtain ⟨B,hBpos,hBF⟩ := hi.isBounded.exists_pos_norm_le
    refine ⟨B,hBpos,?_⟩
    intro j x hx
    have hFx : ‖F x‖≤B := hBF _ (mem_image_of_mem _ (subset_closure hx))
    rw [abs_of_nonneg (hB j x).1]
    exact (hB j x).2.trans ((le_abs_self _).trans hFx)
  have hPDEeventual (E : Set (Space n)) (hE : LocalDomain E Kᶜ) :
      ∀ᶠ j in atTop,WeakPHarmonicPair p E (G j) (Γ j) := by
    obtain ⟨T,_,hET⟩ := hE.2.1.subset_ball_lt 0 (0 : Space n)
    filter_upwards [hRlim.eventually (eventually_ge_atTop T)] with j hj
    apply (hH j).mono _ hE.1
    intro x hx
    exact ⟨ball_subset_ball hj (hET hx),(subset_closure.trans hE.2.2) hx⟩
  obtain ⟨D,hD,hDmono,hDcover,hcofinal⟩ :=
    exists_cofinal_bounded_open_exterior_exhaustion hK hKne
  have hactualSob (j m : ℕ) : SobolevPair p (D m) (G j) (Γ j) :=
    hSob j (D m) (hD m).2.1
  have hMem (j m : ℕ) : MemLp (Γ j) (ENNReal.ofReal p) (volume.restrict (D m)) :=
    (hactualSob j m).2.2.1
  have hscalarLp (m : ℕ) :
      MemLp v (ENNReal.ofReal p) (volume.restrict (D m)) ∧
      Tendsto (fun j=>eLpNorm (G j-v) (ENNReal.ofReal p) (volume.restrict (D m))) atTop (𝓝 0) := by
    obtain ⟨B,hBpos,hbound⟩ := hscalarBound (D m) (hD m).2.1
    letI : IsFiniteMeasure (volume.restrict (D m)) :=
      isFiniteMeasure_restrict.mpr (hD m).2.1.measure_lt_top.ne
    exact raw_scalar_Lp_limit_on_finite_window hp (hD m).1.measurableSet
      (fun j=>(hactualSob j m).2.1.1) hBpos.le hbound (fun x _=>hpoint x)
  have hCauchy (m : ℕ) : CauchySeq (fun j=>(hMem j m).toLp (Γ j)) := by
    obtain ⟨k,hk⟩ := hcofinal (D m) (hD m)
    have hmk : LocalDomain (D m) (D k) := ⟨(hD m).1,(hD m).2.1,hk⟩
    obtain ⟨B,hBpos,hbound⟩ := hscalarBound (D k) (hD k).2.1
    obtain ⟨J,hJ⟩ := eventually_atTop.mp (hPDEeventual (D k) (hD k))
    have hHtail (j : ℕ) : WeakPHarmonicPair p (D k) (G (j+J)) (Γ (j+J)) :=
      hJ (j+J) (by omega)
    have hc := local_gradient_cauchySeq_of_strong_scalar_Lp_limit hp2 (hD k).1 hmk hHtail
      hBpos.le (fun j x hx=>hbound (j+J) x hx)
      (fun j=>(hactualSob (j+J) k).2.1) (hscalarLp k).1
      ((hscalarLp k).2.comp (tendsto_add_atTop_nat J))
    apply green_cauchySeq_of_nat_shift J
    simpa only using! hc
  obtain ⟨g,hg⟩ := exists_actual_local_Lp_limit_of_cauchy_exhaustion hp D
    (fun m=>(hD m).1.measurableSet) hDmono hDcover Γ hMem hCauchy
  have hlimitPDE : WeakPHarmonicPair p Kᶜ v g :=
    weakPHarmonicPair_of_cofinal_local_strong_Lp_limits hp hΩ hD hcofinal hactualSob
      (fun m=>hPDEeventual (D m) (hD m)) (fun m=>(hscalarLp m).1) (fun m=>(hg m).1)
      (fun m=>(hscalarLp m).2) (fun m=>(hg m).2)
  obtain ⟨z,hzc,hvz,_⟩ := hlimitPDE.source_zero.exists_continuous_weak_representative_allp hn
  let w : Space n → ℝ := fun x=>if x∈K then 0 else z x
  have hwz : EqOn w z Kᶜ := by
    intro x hx
    exact if_neg hx
  have hwc : ContinuousOn w Kᶜ := hzc.congr hwz
  have hzwAE : z =ᵐ[volume.restrict Kᶜ] w := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact (hwz hx).symm
  have hvw : v =ᵐ[volume.restrict Kᶜ] w := hvz.trans hzwAE
  have hwK (x : Space n) (hx : x∈K) : w x=0 := if_pos hx
  have hwLo : ∀ x∈Kᶜ,0≤w x := leOn_of_ae_le_continuousOn_actual hΩ continuousOn_const hwc (by
    filter_upwards [hvw] with x hx
    rw [←hx]
    exact (hvB x).1)
  have hwHi : ∀ x∈Kᶜ,w x≤F x := leOn_of_ae_le_continuousOn_actual hΩ hwc hFc.continuousOn (by
    filter_upwards [hvw] with x hx
    rw [←hx]
    exact (hvB x).2)
  have hwB (x : Space n) : 0≤w x ∧ w x≤F x := by
    by_cases hx : x∈K
    · rw [hwK x hx]
      exact ⟨le_rfl,((hB 0 x).1.trans (hB 0 x).2)⟩
    · exact ⟨hwLo x hx,hwHi x hx⟩
  have hwPDE : WeakPHarmonicPair p Kᶜ w g := hlimitPDE.congr_ae hvw EventuallyEq.rfl
  have hstrong (E : Set (Space n)) (hE : LocalDomain E Kᶜ) :
      MemLp w (ENNReal.ofReal p) (volume.restrict E) ∧
      MemLp g (ENNReal.ofReal p) (volume.restrict E) ∧
      Tendsto (fun j=>eLpNorm (G j-w) (ENNReal.ofReal p) (volume.restrict E)) atTop (𝓝 0) ∧
      Tendsto (fun j=>eLpNorm (Γ j-g) (ENNReal.ofReal p) (volume.restrict E)) atTop (𝓝 0) := by
    obtain ⟨m,hm⟩ := hcofinal E hE
    have hμ : volume.restrict E≤volume.restrict (D m) :=
      Measure.restrict_mono (subset_closure.trans hm) le_rfl
    have heAE := ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hE.2.2) hvw
    have hvMem := (hscalarLp m).1.mono_measure hμ
    have hwMem : MemLp w (ENNReal.ofReal p) (volume.restrict E) :=
      (memLp_congr_ae heAE).mp hvMem
    refine ⟨hwMem,(hg m).1.mono_measure hμ,?_,?_⟩
    · have hraw := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hscalarLp m).2
        (fun _=>bot_le) (fun j=>eLpNorm_mono_measure (G j-v) hμ)
      apply hraw.congr'
      exact Eventually.of_forall (fun j=>eLpNorm_congr_ae (EventuallyEq.rfl.sub heAE))
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg m).2
        (fun _=>bot_le) (fun j=>eLpNorm_mono_measure (Γ j-g) hμ)
  exact ⟨v,w,g,hpoint,hvK,hvB,hwc,hvw,hwK,hwB,hwPDE,hstrong⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_selected_weak_limit_of_bounded_annular_family
