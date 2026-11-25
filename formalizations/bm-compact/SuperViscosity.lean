import SuperC1Boundary
import SuperDivergence

/-! Exact manuscript viscosity tests from actual weak C1 subsolutions.
A globally strict upper contact gives a positive compact-boundary gap; lowering
its C2 test and applying genuine weak sub/supersolution comparison gives the
contradiction. No C2 regularity of the weak solution is required or asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem exists_pos_le_on_compact_of_continuousOn_pos {E : Type*} [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) {f : E → ℝ} (hf : ContinuousOn f K)
    (hpos : ∀ x∈K, 0<f x) : ∃ δ : ℝ, 0<δ ∧ ∀ x∈K, δ≤f x := by
  by_cases hne : K.Nonempty
  · obtain ⟨y,hy,hmin⟩ := hK.exists_isMinOn hne hf
    refine ⟨f y/2,half_pos (hpos y hy),?_⟩
    intro x hx
    exact (by linarith [hpos y hy] : f y/2≤f y).trans (hmin hx)
  · refine ⟨1,zero_lt_one,?_⟩
    intro x hx
    exact (hne ⟨x,hx⟩).elim

/-- The local noncritical set of an actual C2 function is open. -/
theorem isOpen_noncritical_region_of_contDiffOn_two {n : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {φ : Space n → ℝ}
    (hφ : ContDiffOn ℝ 2 φ Ω) : IsOpen (Ω ∩ {y | gradient φ y≠0}) := by
  have hc := (contDiffOn_gradient_of_contDiffOn_two hΩ hφ).continuousOn
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  exact inter_mem (hΩ.mem_nhds hy.1)
    ((hc.continuousAt (hΩ.mem_nhds hy.1)).preimage_mem_nhds
      (isOpen_ne.mem_nhds hy.2))

/-- An actual C1 weak subsolution satisfies exactly the manuscript's globally
strict noncritical upper-test convention. Its classical Hessian is never used. -/
theorem WeakPSubsolutionPair.manuscriptViscosity_of_C1
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : WeakPSubsolutionPair p Ω u (gradient u))
    (hu : ContDiffOn ℝ 1 u Ω) (hn : 2≤n) :
    BMCompactAnalytic.IsManuscriptViscosityPSubsolution p Ω u := by
  have hΩ := hw.2.1
  refine ⟨hw.1,hΩ,hu.continuousOn.upperSemicontinuousOn,?_⟩
  intro x hx φ hφ hv hstrict hgφ
  by_contra hnot
  have hneg : BMCompactAnalytic.normalizedPLaplacian p φ x<0 := lt_of_not_ge hnot
  let U : Set (Space n) := Ω ∩ {y | gradient φ y≠0}
  have hU : IsOpen U := isOpen_noncritical_region_of_contDiffOn_two hΩ hφ
  have hxU : x∈U := ⟨hx,hgφ⟩
  let F : Space n → Space n := fun y => pFlux p (gradient φ y)
  have hF : ContDiffOn ℝ 1 F U :=
    contDiffOn_pFlux_gradient_of_contDiffOn_two p hU (hφ.mono inter_subset_left)
      (fun _ hy => hy.2)
  have hdc : ContinuousOn (coordinateDivergence F) U :=
    continuousOn_coordinateDivergence_of_contDiffOn_one hU hF
  have hdivEq : coordinateDivergence F x = BMCompactAnalytic.classicalPLaplacian p φ x := by
    have hd := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)
    unfold coordinateDivergence
    rw [←classicalDivergence_eq_sum_gradient_coordinates hd]
    exact classicalDivergence_pFlux_gradient_eq_classicalPLaplacian p
      (hφ.contDiffAt (hΩ.mem_nhds hx)) hgφ
  have hdivneg : coordinateDivergence F x<0 := by
    rw [hdivEq]
    change ‖gradient φ x‖ ^ (p-2)*BMCompactAnalytic.normalizedPLaplacian p φ x<0
    exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (norm_pos_iff.mpr hgφ) _) hneg
  let V : Set (Space n) := U ∩ {y | coordinateDivergence F y<0}
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    exact inter_mem (hU.mem_nhds hy.1)
      ((hdc.continuousAt (hU.mem_nhds hy.1)).preimage_mem_nhds
        (isOpen_Iio.mem_nhds hy.2))
  have hxV : x∈V := ⟨hxU,hdivneg⟩
  have hVΩ : V ⊆ Ω := inter_subset_left.trans inter_subset_left
  have hφV : ContDiffOn ℝ 2 φ V := hφ.mono hVΩ
  have hsuper : WeakPSupersolutionPair p V φ (gradient φ) := by
    apply weakPSupersolutionPair_of_divergence_nonpos_one hw.1 hV
      (locallySobolevPair_of_contDiffOn_one hw.1 hV (hφV.of_le (by norm_num)))
      (hF.mono inter_subset_left)
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
  have hgapcont : ContinuousOn (fun y => φ y-u y) (frontier D) :=
    (hφ.continuousOn.sub hu.continuousOn).mono hfrontΩ
  have hgappos : ∀ y∈frontier D, 0<φ y-u y := by
    intro y hy
    apply sub_pos.mpr
    apply hstrict y (hfrontΩ hy)
    intro hyx
    subst y
    rw [hD.1.frontier_eq] at hy
    exact hy.2 hxD
  obtain ⟨δ,hδ,hδgap⟩ := exists_pos_le_on_compact_of_continuousOn_pos hfrontK hgapcont hgappos
  let v : Space n → ℝ := fun y => φ y+(-δ)
  have hgradv : gradient v = gradient φ :=
    funext (fun y => BMCompactAnalytic.gradient_add_const φ (-δ) y)
  have hsuperv : WeakPSupersolutionPair p V v (gradient v) := by
    rw [hgradv]
    exact hsuper.add_const (-δ)
  have hsubV := hw.mono hVΩ hV
  have hvc : ContDiffOn ℝ 1 v V := (hφV.of_le (by norm_num)).add contDiffOn_const
  have hboundary : ∀ y∈frontier D, u y≤v y := by
    intro y hy
    have hb := hδgap y hy
    dsimp only [v]
    linarith
  have hle := hsubV.leOn_of_local_C1_boundary_order hsuperv (hu.mono hVΩ) hvc hn hD hboundary x hxD
  dsimp only [v] at hle
  linarith

/-- The existential weak-gradient witness is identified by actual distributional
uniqueness. C1 regularity alone is retained; no noncritical C2 premise for u. -/
theorem IsWeakPHarmonic.manuscriptViscosity_of_C1
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : IsWeakPHarmonic p Ω u) (hu : ContDiffOn ℝ 1 u Ω) (hn : 2≤n) :
    BMCompactAnalytic.IsManuscriptViscosityPSubsolution p Ω u := by
  obtain ⟨g,hw⟩ := hw
  exact (hw.with_classical_gradient hu).subsolution.manuscriptViscosity_of_C1 hu hn

end BMCompactPDE
#print axioms BMCompactPDE.exists_pos_le_on_compact_of_continuousOn_pos
#print axioms BMCompactPDE.isOpen_noncritical_region_of_contDiffOn_two
#print axioms BMCompactPDE.WeakPSubsolutionPair.manuscriptViscosity_of_C1
#print axioms BMCompactPDE.IsWeakPHarmonic.manuscriptViscosity_of_C1
