import SuperComparison

/-! Local C1 boundary comparison. The function only needs to be C1 on an open
neighbourhood of the test-domain closure. Actual compact C1 cutoff density and
nonsmooth W0 truncation construct each positive-excess test. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem contDiff_of_contDiffOn_tsupport_subset {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ∞ω} {Ω : Set E} (hΩ : IsOpen Ω) {f : E → F}
    (hf : ContDiffOn ℝ k f Ω) (hs : tsupport f ⊆ Ω) : ContDiff ℝ k f := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.contDiffAt (hΩ.mem_nhds (hs hx))
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

theorem positivePart_sub_zeroBoundary_of_local_C1_boundary_nonpos
    {n : ℕ} {p : ℝ} (hp : 1 < p) {Ω D : Set (Space n)}
    (hΩ : IsOpen Ω) (hD : LocalDomain D Ω)
    {d : Space n → ℝ} (hd : ContDiffOn ℝ 1 d Ω)
    (hboundary : ∀ x ∈ frontier D, d x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ZeroBoundarySobolevPair p D (fun x => max (d x - ε) 0)
      (fun x => if ε < d x then gradient d x else 0) := by
  let K : Set (Space n) := closure D ∩ {x | ε ≤ d x}
  have hDΩ : D ⊆ Ω := subset_closure.trans hD.2.2
  have hdc : ContinuousOn d (closure D) := hd.continuousOn.mono hD.2.2
  have hK : IsCompact K := hdc.upperSemicontinuousOn.isCompact_inter_preimage_Ici
    hD.2.1.isCompact_closure ε
  have hKΩ : K ⊆ D := by
    intro x hx
    by_contra hxn
    have hxf : x ∈ frontier D := by
      rw [hD.1.frontier_eq]
      exact ⟨hx.1, hxn⟩
    have hb := hboundary x hxf
    have he : ε ≤ d x := hx.2
    linarith
  obtain ⟨f, hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hD.1 hKΩ
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
  have hψOn : ContDiffOn ℝ 1 ψ Ω :=
    ((hχcd.of_le (by simp)).contDiffOn).mul (hd.sub contDiffOn_const)
  have hψcd : ContDiff ℝ 1 ψ := contDiff_of_contDiffOn_tsupport_subset hΩ hψOn
    (tsupport_mul_subset_left.trans (hχs.trans hDΩ))
  have hψc : HasCompactSupport ψ := hχc.mul_right
  have hψs : tsupport ψ ⊆ D := tsupport_mul_subset_left.trans hχs
  have hW := (zeroBoundarySobolevPair_of_contDiff_one_compactSupport
    hp hD.1 hψcd hψc hψs).positivePart
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
  have hGeq : EqOn (positivePartGradient ψ (gradient ψ))
      (fun x => if ε < d x then gradient d x else 0) D := by
    intro x hx
    by_cases hex : ε < d x
    · have hχx := hχ1 x ⟨subset_closure hx, hex.le⟩
      have hψpos : 0 < ψ x := by
        dsimp only [ψ]
        rw [hχx, one_mul]
        exact sub_pos.mpr hex
      have hdAt := hd.continuousOn.continuousAt (hΩ.mem_nhds (hDΩ hx))
      have hN : ∀ᶠ y in 𝓝 x, y ∈ D ∧ ε < d y :=
        inter_mem (hD.1.mem_nhds hx) (hdAt.tendsto.eventually (eventually_gt_nhds hex))
      have heq : ψ =ᶠ[𝓝 x] (fun y => d y - ε) := by
        filter_upwards [hN] with y hy
        have hylt : ε < d y := hy.2
        have hyK : y ∈ K := ⟨subset_closure hy.1, hylt.le⟩
        dsimp only [ψ]
        rw [hχ1 y hyK, one_mul]
      have hgrad : gradient ψ x = gradient d x := by
        unfold gradient
        rw [heq.fderiv_eq, fderiv_sub_const]
      change (if 0 < ψ x then gradient ψ x else 0) =
        (if ε < d x then gradient d x else 0)
      rw [if_pos hψpos, if_pos hex, hgrad]
    · have hd0 : d x - ε ≤ 0 := sub_nonpos.mpr (le_of_not_gt hex)
      have hψ0 : ψ x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hχ0 x) hd0
      change (if 0 < ψ x then gradient ψ x else 0) =
        (if ε < d x then gradient d x else 0)
      rw [if_neg (not_lt.mpr hψ0), if_neg hex]
  apply hW.congr
  · filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
    exact hθeq hx
  · filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
    exact hGeq hx

/-- Ordinary frontier order yields actual comparison of weak sub/supersolutions
on a relatively compact bounded domain, under local C1 regularity. -/
theorem WeakPSubsolutionPair.leOn_of_local_C1_boundary_order
    {n : ℕ} {p : ℝ} {Ω D : Set (Space n)} {u v : Space n → ℝ}
    (hu : WeakPSubsolutionPair p Ω u (gradient u))
    (hv : WeakPSupersolutionPair p Ω v (gradient v))
    (huc : ContDiffOn ℝ 1 u Ω) (hvc : ContDiffOn ℝ 1 v Ω)
    (hn : 2≤n) (hD : LocalDomain D Ω)
    (hboundary : ∀ x∈frontier D, u x≤v x) : ∀ x∈D, u x≤v x := by
  have hDΩ : D ⊆ Ω := subset_closure.trans hD.2.2
  have heps (ε : ℝ) (hε : 0<ε) : ∀ x∈D, u x≤v x+ε := by
    have hw := positivePart_sub_zeroBoundary_of_local_C1_boundary_nonpos
      hu.1 hu.2.1 hD (huc.sub hvc)
      (fun x hx => sub_nonpos.mpr (hboundary x hx)) hε
    have hw' : ZeroBoundarySobolevPair p D (fun x => max (u x-v x-ε) 0)
        (fun x => if v x+ε<u x then gradient u x-gradient v x else 0) := by
      apply hw.congr (Eventually.of_forall (fun _ => rfl))
      filter_upwards [ae_restrict_mem hD.1.measurableSet] with x hx
      have hgrad : gradient (fun y => u y-v y) x = gradient u x-gradient v x := by
        unfold gradient
        rw [fderiv_fun_sub
          (huc.contDiffAt (hu.2.1.mem_nhds (hDΩ hx))).differentiableAt_one
          (hvc.contDiffAt (hu.2.1.mem_nhds (hDΩ hx))).differentiableAt_one]
        exact map_sub (InnerProductSpace.toDual ℝ (Space n)).symm _ _
      have hh : ε<u x-v x ↔ v x+ε<u x := by constructor <;> intro h <;> linarith
      simp only [hh,hgrad]
    exact hu.leOn_add_of_local_W0_excess hv hD hn hw'
      (huc.continuousOn.mono hDΩ) (hvc.continuousOn.mono hDΩ)
  intro x hx
  by_contra hnot
  have hpos : 0<(u x-v x)/2 := by linarith
  have hb := heps ((u x-v x)/2) hpos x hx
  linarith

end BMCompactPDE
#print axioms BMCompactPDE.contDiff_of_contDiffOn_tsupport_subset
#print axioms BMCompactPDE.positivePart_sub_zeroBoundary_of_local_C1_boundary_nonpos
#print axioms BMCompactPDE.WeakPSubsolutionPair.leOn_of_local_C1_boundary_order
