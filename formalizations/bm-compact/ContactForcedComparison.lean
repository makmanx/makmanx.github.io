import ContactForcedDefs

/-! Genuine continuous comparison with the SAME constant forcing. The source
terms cancel in the actual W0 excess test; the function itself is not assumed
classically differentiable. This comparison does not assume existence of any
forced solution or the general viscosity comparison theorem. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem WeakPSourcePair.subsolution {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) : WeakPSourceSubsolutionPair p c Ω u g := by
  refine ⟨hu.1,hu.2.1,hu.2.2.1,?_⟩
  intro D hD θ h hθ _
  obtain ⟨hi,he⟩ := hu.2.2.2 D hD θ h hθ
  exact ⟨hi,he.le⟩

theorem WeakPSourcePair.supersolution {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) : WeakPSourceSupersolutionPair p c Ω u g := by
  refine ⟨hu.1,hu.2.1,hu.2.2.1,?_⟩
  intro D hD θ h hθ _
  obtain ⟨hi,he⟩ := hu.2.2.2 D hD θ h hθ
  exact ⟨hi,he.ge⟩

theorem WeakPSourceSubsolutionPair.mono {n : ℕ} {p c : ℝ} {Ω U : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (hU : U ⊆ Ω) (hUopen : IsOpen U) :
    WeakPSourceSubsolutionPair p c U u g := by
  refine ⟨hu.1,hUopen,hu.2.2.1.mono hU,?_⟩
  intro D hD θ h hθ hnonneg
  exact hu.2.2.2 D ⟨hD.1,hD.2.1,hD.2.2.trans hU⟩ θ h hθ hnonneg

theorem WeakPSourceSupersolutionPair.mono {n : ℕ} {p c : ℝ} {Ω U : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSupersolutionPair p c Ω u g) (hU : U ⊆ Ω) (hUopen : IsOpen U) :
    WeakPSourceSupersolutionPair p c U u g := by
  refine ⟨hu.1,hUopen,hu.2.2.1.mono hU,?_⟩
  intro D hD θ h hθ hnonneg
  exact hu.2.2.2 D ⟨hD.1,hD.2.1,hD.2.2.trans hU⟩ θ h hθ hnonneg

theorem WeakPSourceSubsolutionPair.add_const {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (a : ℝ) :
    WeakPSourceSubsolutionPair p c Ω (fun x => u x+a) g :=
  ⟨hu.1,hu.2.1,hu.2.2.1.add_const hu.1 a,hu.2.2.2⟩

theorem WeakPSourceSubsolutionPair.excess_gradient_ae_zero
    {n : ℕ} {p c ε : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (hv : WeakPSourceSupersolutionPair p c Ω v h)
    (hD : LocalDomain D Ω)
    (hpositive : ZeroBoundarySobolevPair p D
      (fun x => max (u x-v x-ε) 0)
      (fun x => if v x+ε<u x then g x-h x else 0)) :
    (fun x => if v x+ε<u x then g x-h x else 0) =ᵐ[volume.restrict D] 0 := by
  let θ : Space n → ℝ := fun x => max (u x-v x-ε) 0
  let w : Space n → Space n := fun x => if v x+ε<u x then g x-h x else 0
  have hθ : ZeroBoundarySobolevPair p D θ w := hpositive
  have hnonnegθ : ∀ᵐ x ∂volume.restrict D, 0≤θ x :=
    Eventually.of_forall (fun x => le_max_right _ _)
  obtain ⟨hgi,hgle⟩ := hu.2.2.2 D hD θ w hθ hnonnegθ
  obtain ⟨hhi,hhge⟩ := hv.2.2.2 D hD θ w hθ hnonnegθ
  let pairing : Space n → ℝ := fun x =>
    inner ℝ (pFlux p (g x)-pFlux p (h x)) (w x)
  have hpair : pairing = fluxPairing p g w-fluxPairing p h w := by
    funext x
    simp only [pairing,fluxPairing,Pi.sub_apply,inner_sub_left]
  have hpi : Integrable pairing (volume.restrict D) := by
    rw [hpair]
    exact hgi.sub hhi
  have hple : (∫ x in D, pairing x)≤0 := by
    rw [hpair]
    simp only [Pi.sub_apply]
    rw [integral_sub hgi hhi]
    linarith
  have hnonneg : 0≤ᵐ[volume.restrict D] pairing := by
    apply Eventually.of_forall
    intro x
    by_cases hx : v x+ε<u x
    · simp only [pairing,w,if_pos hx]
      exact pFlux_monotonicity hu.1 (g x) (h x)
    · simp only [pairing,w,if_neg hx,inner_zero_right]
      exact le_rfl
  have hpeq : (∫ x in D, pairing x)=0 :=
    le_antisymm hple (integral_nonneg_of_ae hnonneg)
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hpi).1 hpeq
  change w =ᵐ[volume.restrict D] 0
  filter_upwards [hzero] with x hx
  by_cases hpos : v x+ε<u x
  · have hgh : g x=h x :=
      (pFlux_pairing_eq_zero_iff hu.1 (g x) (h x)).1 (by
        simpa only [pairing,w,if_pos hpos,Pi.zero_apply] using hx)
    simp only [w,if_pos hpos,hgh,sub_self,Pi.zero_apply]
  · simp only [w,if_neg hpos,Pi.zero_apply]

theorem WeakPSourceSubsolutionPair.leOn_add_of_local_W0_excess
    {n : ℕ} {p c ε : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (hv : WeakPSourceSupersolutionPair p c Ω v h)
    (hD : LocalDomain D Ω) (hn : 2≤n)
    (hpositive : ZeroBoundarySobolevPair p D
      (fun x => max (u x-v x-ε) 0)
      (fun x => if v x+ε<u x then g x-h x else 0))
    (huc : ContinuousOn u D) (hvc : ContinuousOn v D) :
    ∀ x∈D, u x≤v x+ε := by
  have hw := hu.excess_gradient_ae_zero hv hD hpositive
  have hθc : ContinuousOn (fun x => max (u x-v x-ε) 0) D :=
    ((huc.sub hvc).sub continuousOn_const).sup continuousOn_const
  have hz := hpositive.eqOn_zero_of_gradient_ae_zero hn hD.1 hD.2.1 hw hθc
  intro x hx
  have hmax : max (u x-v x-ε) 0=0 := hz hx
  have hd : u x-v x-ε≤0 := (le_max_left _ _).trans hmax.le
  linarith

theorem WeakPSourceSubsolutionPair.leOn_of_continuous_boundary_order
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)} {u v : Space n → ℝ}
    {g h : Space n → Space n}
    (hu : WeakPSourceSubsolutionPair p c Ω u g) (hv : WeakPSourceSupersolutionPair p c Ω v h)
    (huc : ContinuousOn u Ω) (hvc : ContinuousOn v Ω)
    (hn : 2≤n) (hD : LocalDomain D Ω)
    (hboundary : ∀ x∈frontier D, u x≤v x) : ∀ x∈D, u x≤v x := by
  have hDΩ : D ⊆ Ω := subset_closure.trans hD.2.2
  have hSu := hu.2.2.1 D hD
  have hSv := hv.2.2.1 D hD
  have hSd : SobolevPair p D (fun x => u x-v x) (fun x => g x-h x) := by
    have hs := hSu.add (hSv.smul (-1))
    exact hs.congr (Eventually.of_forall (fun x => by simp [sub_eq_add_neg]))
      (Eventually.of_forall (fun x => by simp [sub_eq_add_neg]))
  have heps (ε : ℝ) (hε : 0<ε) : ∀ x∈D, u x≤v x+ε := by
    have hw := positivePart_sub_zeroBoundary_of_continuous_sobolev_boundary_nonpos
      hu.1 hD.1 hD.2.1 hSd ((huc.sub hvc).mono hD.2.2)
      (fun x hx => sub_nonpos.mpr (hboundary x hx)) hε
    have hw' : ZeroBoundarySobolevPair p D (fun x => max (u x-v x-ε) 0)
        (fun x => if v x+ε<u x then g x-h x else 0) := by
      apply hw.congr (Eventually.of_forall (fun _ => rfl))
      exact Eventually.of_forall (fun x => by
        have hh : ε<u x-v x ↔ v x+ε<u x := by constructor <;> intro h <;> linarith
        simp only [hh])
    exact hu.leOn_add_of_local_W0_excess hv hD hn hw'
      (huc.mono hDΩ) (hvc.mono hDΩ)
  intro x hx
  by_contra hnot
  have hpos : 0<(u x-v x)/2 := by linarith
  have hb := heps ((u x-v x)/2) hpos x hx
  linarith


/-- A C1 actual flux with the actual divergence lower bound is a full-W0
source subsolution, even when its gradient vanishes. -/
theorem weakPSourceSubsolutionPair_of_divergence_ge_one
    {n : ℕ} {p c : ℝ} (hp : 1<p) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hSob : LocallySobolevPair p Ω u g)
    (hF : ContDiffOn ℝ 1 (fun x => pFlux p (g x)) Ω)
    (hdiv : ∀ x∈Ω, -c ≤ coordinateDivergence (fun y => pFlux p (g y)) x) :
    WeakPSourceSubsolutionPair p c Ω u g := by
  refine ⟨hp,hΩ,hSob,?_⟩
  intro D hD θ h hθ hθ0
  letI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hD.2.1.measure_lt_top.ne
  have hθi : Integrable θ (volume.restrict D) :=
    MemLp.integrable (ENNReal.one_le_ofReal.mpr hp.le) hθ.1.2.1
  obtain ⟨hiF,hib,heq⟩ := integral_inner_eq_neg_divergence_zeroBoundary_one hp hΩ hD hF hθ
  refine ⟨hiF,?_⟩
  change (∫ x in D, inner ℝ (pFlux p (g x)) (h x)) ≤ c*(∫ x in D, θ x)
  rw [heq,←integral_const_mul c]
  have hle : (∫ x in D, -coordinateDivergence (fun y => pFlux p (g y)) x*θ x) ≤
      ∫ x in D, c*θ x := by
    apply integral_mono_ae (hib.neg.congr (Eventually.of_forall (fun x => by simp only [Pi.neg_apply,neg_mul]))) (hθi.const_mul c)
    filter_upwards [hθ0,ae_restrict_mem hD.1.measurableSet] with x hx0 hx
    exact mul_le_mul_of_nonneg_right (by linarith [hdiv x (hD.2.2 (subset_closure hx))]) hx0
  simpa only [neg_mul,integral_neg] using hle

theorem WeakPSourceSupersolutionPair.le_neg_divergence_at_strict_contact
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : WeakPSourceSupersolutionPair p c Ω v h) (hvc : ContinuousOn v Ω)
    (hn : 2≤n) {x : Space n} (hx : x∈Ω)
    {φ : Space n → ℝ} (hφ : ContDiffOn ℝ 1 φ Ω)
    (hF : ContDiffOn ℝ 1 (fun y => pFlux p (gradient φ y)) Ω)
    (htouch : v x=φ x) (hstrict : ∀ y∈Ω, y≠x → φ y<v y) :
    c ≤ -coordinateDivergence (fun y => pFlux p (gradient φ y)) x := by
  by_contra hnot
  have hgt : -c < coordinateDivergence (fun y => pFlux p (gradient φ y)) x := by
    linarith [lt_of_not_ge hnot]
  let F : Space n → Space n := fun y => pFlux p (gradient φ y)
  have hdc : ContinuousOn (coordinateDivergence F) Ω :=
    continuousOn_coordinateDivergence_of_contDiffOn_one hv.2.1 hF
  let V : Set (Space n) := Ω ∩ {y | -c<coordinateDivergence F y}
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    exact inter_mem (hv.2.1.mem_nhds hy.1)
      ((hdc.continuousAt (hv.2.1.mem_nhds hy.1)).preimage_mem_nhds
        (isOpen_Ioi.mem_nhds hy.2))
  have hxV : x∈V := ⟨hx,hgt⟩
  have hVΩ : V ⊆ Ω := inter_subset_left
  have hφV : ContDiffOn ℝ 1 φ V := hφ.mono hVΩ
  have hsub : WeakPSourceSubsolutionPair p c V φ (gradient φ) := by
    apply weakPSourceSubsolutionPair_of_divergence_ge_one hv.1 hV
      (locallySobolevPair_of_contDiffOn_one hv.1 hV hφV) (hF.mono hVΩ)
    intro y hy
    exact hy.2.le
  obtain ⟨η,hη,hηV⟩ := Metric.isOpen_iff.mp hV x hxV
  let R : ℝ := η/2
  have hR : 0<R := half_pos hη
  have hRη : R<η := half_lt_self hη
  let D : Set (Space n) := ball x R
  have hD : LocalDomain D V := by
    refine ⟨isOpen_ball,isBounded_ball,?_⟩
    intro y hy
    apply hηV
    have hclosed : y∈closedBall x R := closure_ball_subset_closedBall hy
    exact lt_of_le_of_lt (mem_closedBall.mp hclosed) hRη
  have hxD : x∈D := mem_ball_self hR
  have hfrontV : frontier D ⊆ V := frontier_subset_closure.trans hD.2.2
  have hfrontΩ : frontier D ⊆ Ω := hfrontV.trans hVΩ
  have hfrontK : IsCompact (frontier D) :=
    hD.2.1.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hgapcont : ContinuousOn (fun y => v y-φ y) (frontier D) :=
    (hvc.sub hφ.continuousOn).mono hfrontΩ
  have hgappos : ∀ y∈frontier D, 0<v y-φ y := by
    intro y hy
    apply sub_pos.mpr
    apply hstrict y (hfrontΩ hy)
    intro hyx
    subst y
    rw [hD.1.frontier_eq] at hy
    exact hy.2 hxD
  obtain ⟨δ,hδ,hδgap⟩ := exists_pos_le_on_compact_of_continuousOn_pos hfrontK hgapcont hgappos
  let w : Space n → ℝ := fun y => φ y+δ
  have hsubw : WeakPSourceSubsolutionPair p c V w (gradient φ) := hsub.add_const δ
  have hsupV := hv.mono hVΩ hV
  have hboundary : ∀ y∈frontier D, w y≤v y := by
    intro y hy
    have hb := hδgap y hy
    dsimp only [w]
    linarith
  have hle := hsubw.leOn_of_continuous_boundary_order hsupV
    (hφV.continuousOn.add continuousOn_const) (hvc.mono hVΩ) hn hD hboundary x hxD
  dsimp only [w] at hle
  linarith

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.subsolution
#print axioms BMCompactPDE.WeakPSourcePair.supersolution
#print axioms BMCompactPDE.WeakPSourceSubsolutionPair.mono
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.mono
#print axioms BMCompactPDE.WeakPSourceSubsolutionPair.add_const
#print axioms BMCompactPDE.WeakPSourceSubsolutionPair.excess_gradient_ae_zero
#print axioms BMCompactPDE.WeakPSourceSubsolutionPair.leOn_add_of_local_W0_excess
#print axioms BMCompactPDE.WeakPSourceSubsolutionPair.leOn_of_continuous_boundary_order
#print axioms BMCompactPDE.weakPSourceSubsolutionPair_of_divergence_ge_one
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.le_neg_divergence_at_strict_contact
