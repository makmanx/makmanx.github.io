import UpstreamGreenScalarLimit
import UpstreamGreenGradientCauchy
import UpstreamGreenExteriorExhaustion
import UpstreamGreenLocalLpLimit
import UpstreamGreenLocalPDEClosure
import UpstreamGreenScalarLp

/-! Actual strong local weak-gradient limit and weak PDE of the constructed
supercritical annular scalar limit. Scalar convergence, gradient Cauchy data,
one raw gradient field, its strong convergence and the limit PDE are all
derived. No candidate family, convergence, gradient ceiling or limit field is
an input. Global boundary continuity and the bounded Green remainder remain
separate compositions with the same retained annular family. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

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

set_option maxHeartbeats 1800000 in
theorem exists_canonical_annular_green_weak_limit_supercritical
    {n : ℕ} {p : ℝ} (hn : 2≤n) (hnp : (n : ℝ)<p)
    {K : Set (Space n)} (hK : IsCompact K) (h0 : (0 : Space n)∈K) :
    ∃ R : ℕ → ℝ,∃ G : ℕ → Space n → ℝ,∃ Γ : ℕ → Space n → Space n,
      ∃ v : Space n → ℝ,∃ g : Space n → Space n,
      (∀ j,0<R j ∧ K⊆ball 0 (R j)) ∧ StrictMono R ∧ Tendsto R atTop atTop ∧
      (∀ j,Continuous (G j)) ∧ (∀ j x,x∈K → G j x=0) ∧
      (∀ j x,x∉ball 0 (R j) → G j x=fundamentalRadialValue n (canonicalSphereArea n) p (R j)) ∧
      (∀ j,MemLp (Γ j) (ENNReal.ofReal p) volume) ∧
      (∀ j B,Bornology.IsBounded B → SobolevPair p B (G j) (Γ j)) ∧
      (∀ j,WeakPHarmonicPair p (ball 0 (R j)\K) (G j) (Γ j)) ∧
      (∀ j x,0≤G j x ∧ G j x≤fundamentalPotential n (canonicalSphereArea n) p x) ∧
      (∀ j k,j≤k → ∀ x∈ball 0 (R j),G k x≤G j x) ∧
      ContinuousOn v Kᶜ ∧ (∀ x,Tendsto (fun j=>G j x) atTop (𝓝 (v x))) ∧
      (∀ x∈K,v x=0) ∧ (∀ x,0≤v x ∧ v x≤fundamentalPotential n (canonicalSphereArea n) p x) ∧
      (∀ D : Set (Space n),LocalDomain D Kᶜ → TendstoUniformlyOn G v atTop (closure D)) ∧
      WeakPHarmonicPair p Kᶜ v g ∧
      ∀ D : Set (Space n),LocalDomain D Kᶜ →
        MemLp g (ENNReal.ofReal p) (volume.restrict D) ∧
        Tendsto (fun j=>eLpNorm (Γ j-g) (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0) := by
  classical
  obtain ⟨R,G,Γ,v,hR,hRmono,hRlim,hGc,hGK,hGout,hΓ,hSob,hH,hB,horder,hvc,hpoint,hvK,hvB,huni⟩ :=
    exists_canonical_annular_green_scalar_limit_supercritical hn hnp hK h0
  have hnR : 1<(n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2) hn)
  have hp : 1<p := hnR.trans hnp
  have hp2 : 2≤p := (show (2 : ℝ)≤(n : ℝ) by exact_mod_cast hn).trans hnp.le
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have hΩ : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  have hFcont : Continuous (fundamentalPotential n (canonicalSphereArea n) p : Space n → ℝ) :=
    continuous_fundamentalPotential_supercritical n (canonicalSphereArea n) hnR hnp
  have hscalarBound (E : Set (Space n)) (hEb : Bornology.IsBounded E) :
      ∃ B : ℝ,0<B ∧ ∀ j x,x∈E → |G j x|≤B := by
    have hi : IsCompact ((fundamentalPotential n (canonicalSphereArea n) p) '' closure E) :=
      hEb.isCompact_closure.image hFcont
    obtain ⟨B,hBpos,hBF⟩ := hi.isBounded.exists_pos_norm_le
    refine ⟨B,hBpos,?_⟩
    intro j x hx
    have hFx : ‖fundamentalPotential n (canonicalSphereArea n) p x‖≤B :=
      hBF _ (mem_image_of_mem _ (subset_closure hx))
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
    exists_cofinal_bounded_open_exterior_exhaustion hK ⟨0,h0⟩
  have hactualSob (j m : ℕ) : SobolevPair p (D m) (G j) (Γ j) :=
    hSob j (D m) (hD m).2.1
  have hMem (j m : ℕ) : MemLp (Γ j) (ENNReal.ofReal p) (volume.restrict (D m)) :=
    (hactualSob j m).2.2.1
  have hCauchy (m : ℕ) : CauchySeq (fun j=>(hMem j m).toLp (Γ j)) := by
    obtain ⟨k,hk⟩ := hcofinal (D m) (hD m)
    have hmk : LocalDomain (D m) (D k) := ⟨(hD m).1,(hD m).2.1,hk⟩
    obtain ⟨B,hBpos,hbound⟩ := hscalarBound (D k) (hD k).2.1
    obtain ⟨J,hJ⟩ := eventually_atTop.mp (hPDEeventual (D k) (hD k))
    have hHtail (j : ℕ) : WeakPHarmonicPair p (D k) (G (j+J)) (Γ (j+J)) :=
      hJ (j+J) (by omega)
    have hlimtail : TendstoUniformlyOn (fun j=>G (j+J)) v atTop (D k) := by
      intro V hV
      exact (tendsto_add_atTop_nat J).eventually (((huni (D k) (hD k)).mono subset_closure) V hV)
    have hc := local_gradient_cauchySeq_of_uniform_scalar_limit hp2 (hD k).1 hmk hHtail
      hBpos.le (fun j x hx=>hbound (j+J) x hx) hlimtail
    apply green_cauchySeq_of_nat_shift J
    simpa only using! hc
  obtain ⟨g,hg⟩ := exists_actual_local_Lp_limit_of_cauchy_exhaustion hp D
    (fun m=>(hD m).1.measurableSet) hDmono hDcover Γ hMem hCauchy
  have hscalarLp (m : ℕ) :
      MemLp v (ENNReal.ofReal p) (volume.restrict (D m)) ∧
      Tendsto (fun j=>eLpNorm (G j-v) (ENNReal.ofReal p) (volume.restrict (D m))) atTop (𝓝 0) := by
    obtain ⟨B,hBpos,hbound⟩ := hscalarBound (D m) (hD m).2.1
    exact scalar_Lp_limit_on_bounded_of_pointwise_bounded hp (hD m).2.1 (hD m).1.measurableSet
      (fun j=>(hGc j).continuousOn) (hvc.mono (hD m).2.2) hBpos.le hbound (fun x _=>hpoint x)
  have hlimitPDE : WeakPHarmonicPair p Kᶜ v g :=
    weakPHarmonicPair_of_cofinal_local_strong_Lp_limits hp hΩ hD hcofinal hactualSob
      (fun m=>hPDEeventual (D m) (hD m)) (fun m=>(hscalarLp m).1) (fun m=>(hg m).1)
      (fun m=>(hscalarLp m).2) (fun m=>(hg m).2)
  have hstrong (E : Set (Space n)) (hE : LocalDomain E Kᶜ) :
      MemLp g (ENNReal.ofReal p) (volume.restrict E) ∧
      Tendsto (fun j=>eLpNorm (Γ j-g) (ENNReal.ofReal p) (volume.restrict E)) atTop (𝓝 0) := by
    obtain ⟨m,hm⟩ := hcofinal E hE
    have hμ : volume.restrict E≤volume.restrict (D m) :=
      Measure.restrict_mono (subset_closure.trans hm) le_rfl
    refine ⟨(hg m).1.mono_measure hμ,?_⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hg m).2
      (fun _=>bot_le) (fun j=>eLpNorm_mono_measure (Γ j-g) hμ)
  exact ⟨R,G,Γ,v,g,hR,hRmono,hRlim,hGc,hGK,hGout,hΓ,hSob,hH,hB,horder,hvc,hpoint,hvK,hvB,huni,
    hlimitPDE,hstrong⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_canonical_annular_green_weak_limit_supercritical
