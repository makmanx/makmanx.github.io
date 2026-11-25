import SuperViscosity
import SuperQuartic
import RootCompactSobolevDensity
/-! Eight supporting proof bodies composed once from four independent
development scopes. Readable original segments are provenance, not
additional build targets or proof counts. Actual distributional
Sobolev localization and density are proved dependencies, not premises.
Only continuity of the actual weak representative is assumed. -/

/-! Provenance segment: SuperContinuousBoundary -/
section SuperScopeSuperContinuousBoundary
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem positivePart_sub_zeroBoundary_of_continuous_sobolev_boundary_nonpos
    {n : ℕ} {p : ℝ} (hp : 1 < p) {D : Set (Space n)}
    (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {d : Space n → ℝ} {g : Space n → Space n}
    (hd : SobolevPair p D d g) (hdc : ContinuousOn d (closure D))
    (hboundary : ∀ x ∈ frontier D, d x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ZeroBoundarySobolevPair p D (fun x => max (d x - ε) 0)
      (fun x => if ε < d x then g x else 0) := by
  let K : Set (Space n) := closure D ∩ {x | ε ≤ d x}
  have hK : IsCompact K := hdc.upperSemicontinuousOn.isCompact_inter_preimage_Ici
    hDb.isCompact_closure ε
  have hKΩ : K ⊆ D := by
    intro x hx
    by_contra hxn
    have hxf : x ∈ frontier D := by
      rw [hD.frontier_eq]
      exact ⟨hx.1, hxn⟩
    have hb := hboundary x hxf
    have he : ε ≤ d x := hx.2
    linarith
  obtain ⟨f, hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hD hKΩ
  let χ : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hχcd : ContDiff ℝ ∞ χ :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).comp hf.1
  have hχc : HasCompactSupport χ := hf.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)))
  have hχs : tsupport χ ⊆ D :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1
  have hχ0 (x : Space n) : 0 ≤ χ x := Real.smoothTransition.nonneg _
  have hχ1 (x : Space n) (hx : x ∈ K) : χ x = 1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)
  let ψ : Space n → ℝ := fun x => χ x * (d x - ε)
  let G : Space n → Space n := fun x => χ x • g x+(d x-ε) • gradient χ x
  have hsd : SobolevPair p D (fun x => d x-ε) g := by
    have hs := hd.add (sobolevPair_const hp hDb (-ε))
    exact hs.congr (Eventually.of_forall (fun x => by simp [sub_eq_add_neg]))
      (Eventually.of_forall (fun x => by simp))
  have hW := (hsd.mul_smooth_compactSupport_zeroBoundary hD hχcd hχc hχs).positivePart
  have hθeq : EqOn (fun x => max (ψ x) 0) (fun x => max (d x - ε) 0) D := by
    intro x hx
    change max (ψ x) 0 = max (d x - ε) 0
    by_cases hex : ε < d x
    · have hχx := hχ1 x ⟨subset_closure hx, hex.le⟩
      dsimp only [ψ]
      rw [hχx, one_mul]
    · have hd0 : d x - ε ≤ 0 := sub_nonpos.mpr (le_of_not_gt hex)
      have hψ0 : ψ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hχ0 x) hd0
      rw [max_eq_right hψ0, max_eq_right hd0]
  have hGeq : EqOn (positivePartGradient ψ G)
      (fun x => if ε < d x then g x else 0) D := by
    intro x hx
    by_cases hex : ε < d x
    · have hχx := hχ1 x ⟨subset_closure hx, hex.le⟩
      have hψpos : 0 < ψ x := by
        dsimp only [ψ]
        rw [hχx, one_mul]
        exact sub_pos.mpr hex
      have hdAt := (hdc.mono subset_closure).continuousAt (hD.mem_nhds hx)
      have hN : ∀ᶠ y in 𝓝 x, y ∈ D ∧ ε < d y :=
        inter_mem (hD.mem_nhds hx) (hdAt.tendsto.eventually (eventually_gt_nhds hex))
      have heqχ : χ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
        filter_upwards [hN] with y hy
        exact hχ1 y ⟨subset_closure hy.1,hy.2.le⟩
      have hgradχ : gradient χ x=0 := by
        unfold gradient
        rw [heqχ.fderiv_eq]
        simp
      have hGx : G x=g x := by
        simp only [G,hχx,hgradχ,one_smul,smul_zero,add_zero]
      change (if 0 < ψ x then G x else 0) =
        (if ε < d x then g x else 0)
      rw [if_pos hψpos, if_pos hex,hGx]
    · have hd0 : d x - ε ≤ 0 := sub_nonpos.mpr (le_of_not_gt hex)
      have hψ0 : ψ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hχ0 x) hd0
      change (if 0 < ψ x then G x else 0) =
        (if ε < d x then g x else 0)
      rw [if_neg (not_lt.mpr hψ0), if_neg hex]
  apply hW.congr
  · filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    exact hθeq hx
  · filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    exact hGeq hx

/-- General continuous weak sub/supersolution comparison, with actual local
Sobolev test construction. No C1 assumption is present. -/
theorem WeakPSubsolutionPair.leOn_of_continuous_boundary_order
    {n : ℕ} {p : ℝ} {Ω D : Set (Space n)} {u v : Space n → ℝ}
    {g h : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g) (hv : WeakPSupersolutionPair p Ω v h)
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

end BMCompactPDE
#print axioms BMCompactPDE.positivePart_sub_zeroBoundary_of_continuous_sobolev_boundary_nonpos
#print axioms BMCompactPDE.WeakPSubsolutionPair.leOn_of_continuous_boundary_order
end
end SuperScopeSuperContinuousBoundary

/-! Provenance segment: SuperContinuousViscosity -/
section SuperScopeSuperContinuousViscosity
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE
/-- A continuous actual weak subsolution satisfies the manuscript globally
strict noncritical upper-test convention. No differentiability of u is assumed. -/
theorem WeakPSubsolutionPair.manuscriptViscosity_of_continuous
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hw : WeakPSubsolutionPair p Ω u g)
    (hu : ContinuousOn u Ω) (hn : 2≤n) :
    BMCompactAnalytic.IsManuscriptViscosityPSubsolution p Ω u := by
  have hΩ := hw.2.1
  refine ⟨hw.1,hΩ,hu.upperSemicontinuousOn,?_⟩
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
    (hφ.continuousOn.sub hu).mono hfrontΩ
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
  have hle := hsubV.leOn_of_continuous_boundary_order hsuperv (hu.mono hVΩ) hvc.continuousOn hn hD hboundary x hxD
  dsimp only [v] at hle
  linarith

/-- The existential actual weak field is used directly. No C1 or C2
regularity of u is assumed; its actual continuous representative is explicit. -/
theorem IsWeakPHarmonic.manuscriptViscosity_of_continuous
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : IsWeakPHarmonic p Ω u) (hu : ContinuousOn u Ω) (hn : 2≤n) :
    BMCompactAnalytic.IsManuscriptViscosityPSubsolution p Ω u := by
  obtain ⟨g,hw⟩ := hw
  exact hw.subsolution.manuscriptViscosity_of_continuous hu hn

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSubsolutionPair.manuscriptViscosity_of_continuous
#print axioms BMCompactPDE.IsWeakPHarmonic.manuscriptViscosity_of_continuous
end
end SuperScopeSuperContinuousViscosity

/-! Provenance segment: SuperContinuousLocalViscosity -/
section SuperScopeSuperContinuousLocalViscosity
noncomputable section
set_option autoImplicit false
open Set Filter InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactPDE

theorem WeakPSubsolutionPair.viscosity_of_continuous
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hw : WeakPSubsolutionPair p Ω u g)
    (hu : ContinuousOn u Ω) (hn : 2≤n) :
    BMCompactAnalytic.IsViscosityPSubsolution p Ω u := by
  refine ⟨hw.1,hw.2.1,hu.upperSemicontinuousOn,?_⟩
  intro x hx φ hφ hv hupper hg
  have hex : ∃ U∈𝓝 x, ContDiffOn ℝ 2 φ U := hφ.contDiffOn le_rfl (by simp)
  obtain ⟨U,hUn,hφU⟩ := hex
  obtain ⟨V,hVU,hV,hxV⟩ := mem_nhds_iff.mp hUn
  obtain ⟨T,hTupper,hT,hxT⟩ := mem_nhds_iff.mp hupper
  let D : Set (Space n) := Ω ∩ V ∩ T
  have hD : IsOpen D := (hw.2.1.inter hV).inter hT
  have hxD : x∈D := ⟨⟨hx,hxV⟩,hxT⟩
  have hDΩ : D ⊆ Ω := inter_subset_left.trans inter_subset_left
  have hDU : D ⊆ U := (inter_subset_left.trans inter_subset_right).trans hVU
  have hlocal := (hw.mono hDΩ hD).manuscriptViscosity_of_continuous (hu.mono hDΩ) hn
  let ψ : Space n → ℝ := fun y => φ y+BMCompactAnalytic.strictContactQuartic x y
  have hq : ContDiff ℝ 2 (BMCompactAnalytic.strictContactQuartic x) :=
    (BMCompactAnalytic.contDiff_strictContactQuartic x).of_le (by decide)
  have hψ : ContDiffOn ℝ 2 ψ D := (hφU.mono hDU).add hq.contDiffOn
  have hval : u x=ψ x := by
    dsimp only [ψ]
    rw [BMCompactAnalytic.strictContactQuartic_self,add_zero]
    exact hv
  have hstrict : ∀ y∈D, y≠x → u y<ψ y := by
    intro y hy hyx
    have hle : u y≤φ y := hTupper hy.2
    have hpos := BMCompactAnalytic.strictContactQuartic_pos hyx
    dsimp only [ψ]
    linarith
  have hgrad : gradient ψ x≠0 := by
    simpa only [ψ,BMCompactAnalytic.gradient_add_strictContactQuartic_self
      (hφ.differentiableAt (by norm_num))] using hg
  have htest := hlocal.2.2.2 x hxD ψ hψ hval hstrict hgrad
  simpa only [ψ,BMCompactAnalytic.normalizedPLaplacian_add_strictContactQuartic_self p hφ] using htest

/-- Actual continuous weak p-harmonicity implies the strong local
noncritical-test viscosity condition, with no C1/C2 regularity of u. -/
theorem IsWeakPHarmonic.viscosity_of_continuous
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ}
    (hw : IsWeakPHarmonic p Ω u) (hu : ContinuousOn u Ω) (hn : 2≤n) :
    BMCompactAnalytic.IsViscosityPSubsolution p Ω u := by
  obtain ⟨g,hw⟩ := hw
  exact hw.subsolution.viscosity_of_continuous hu hn

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSubsolutionPair.viscosity_of_continuous
#print axioms BMCompactPDE.IsWeakPHarmonic.viscosity_of_continuous
end
end SuperScopeSuperContinuousLocalViscosity

/-! Provenance segment: SuperContinuousBoundedComparison -/
section SuperScopeSuperContinuousBoundedComparison
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace BMCompactPDE

theorem WeakPSubsolutionPair.leOn_of_continuous_bounded_boundary_order
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u v : Space n → ℝ}
    {g h : Space n → Space n}
    (hu : WeakPSubsolutionPair p Ω u g)
    (hv : WeakPSupersolutionPair p Ω v h)
    (hucb : ContinuousOn u (closure Ω)) (hvcb : ContinuousOn v (closure Ω))
    (hn : 2≤n) (hΩb : Bornology.IsBounded Ω)
    (hboundary : ∀ x∈frontier Ω, u x≤v x) : ∀ x∈Ω, u x≤v x := by
  intro x hx
  by_contra hnot
  let ε : ℝ := (u x-v x)/2
  have hε : 0<ε := by dsimp only [ε]; linarith
  have hex : ε<u x-v x := by dsimp only [ε]; linarith
  let K : Set (Space n) := closure Ω ∩ {y | ε≤u y-v y}
  have hK : IsCompact K :=
    (hucb.sub hvcb).upperSemicontinuousOn.isCompact_inter_preimage_Ici hΩb.isCompact_closure ε
  have hKΩ : K ⊆ Ω := by
    intro y hy
    by_contra hyn
    have hyf : y∈frontier Ω := by
      rw [hu.2.1.frontier_eq]
      exact ⟨hy.1,hyn⟩
    have hb := hboundary y hyf
    have hd := hy.2
    change ε≤u y-v y at hd
    linarith
  have hxK : x∈K := ⟨subset_closure hx,hex.le⟩
  obtain ⟨δ,hδ,hδΩ⟩ := hK.exists_cthickening_subset_open hu.2.1 hKΩ
  let D : Set (Space n) := thickening δ K
  have hKD : K ⊆ D := self_subset_thickening hδ K
  have hD : LocalDomain D Ω :=
    ⟨isOpen_thickening,hK.isBounded.thickening,
      (closure_thickening_subset_cthickening δ K).trans hδΩ⟩
  let w : Space n → ℝ := fun y => v y+ε
  have hsuperw : WeakPSupersolutionPair p Ω w h := hv.add_const ε
  have hwb : ∀ y∈frontier D, u y≤w y := by
    intro y hy
    have hyΩ : y∈Ω := hD.2.2 (frontier_subset_closure hy)
    have hynK : y∉K := by
      intro hyK
      have hyD := hKD hyK
      rw [hD.1.frontier_eq] at hy
      exact hy.2 hyD
    have hlt : u y-v y<ε := by
      by_contra hge
      exact hynK ⟨subset_closure hyΩ,le_of_not_gt hge⟩
    dsimp only [w]
    linarith
  have hle := hu.leOn_of_continuous_boundary_order hsuperw
    (hucb.mono subset_closure) ((hvcb.add continuousOn_const).mono subset_closure)
    hn hD hwb x (hKD hxK)
  dsimp only [w,ε] at hle
  linarith

/-- Existential actual weak fields are used directly; continuity on the
closure suffices for ordinary bounded-domain weak comparison. -/
theorem IsWeakPHarmonic.leOn_of_continuous_bounded_boundary_order
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u v : Space n → ℝ}
    (hu : IsWeakPHarmonic p Ω u) (hv : IsWeakPHarmonic p Ω v)
    (hucb : ContinuousOn u (closure Ω)) (hvcb : ContinuousOn v (closure Ω))
    (hn : 2≤n) (hΩb : Bornology.IsBounded Ω)
    (hboundary : ∀ x∈frontier Ω, u x≤v x) : ∀ x∈Ω, u x≤v x := by
  obtain ⟨g,hu⟩ := hu
  obtain ⟨h,hv⟩ := hv
  exact hu.subsolution.leOn_of_continuous_bounded_boundary_order
    hv.supersolution hucb hvcb hn hΩb hboundary

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSubsolutionPair.leOn_of_continuous_bounded_boundary_order
#print axioms BMCompactPDE.IsWeakPHarmonic.leOn_of_continuous_bounded_boundary_order
end
end SuperScopeSuperContinuousBoundedComparison
