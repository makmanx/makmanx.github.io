import SmoothPositivePartAdmissibility
import WeakAffine

/-! Actual bounded boundary comparison in the smooth subcase. Positive
truncations of every ε-excess are constructed in the concrete W0 graph using
an actual C∞ compact-support cutoff. The boundary condition is ordinary
pointwise order on the frontier. General nonsmooth Sobolev chain rules and
comparison remain separate obligations. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace BMCompactPDE

theorem positivePart_sub_zeroBoundary_of_boundary_nonpos
    {n : ℕ} {p : ℝ} (hp : 1 < p) {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {d : Space n → ℝ} (hd : ContDiff ℝ ∞ d)
    (hboundary : ∀ x ∈ frontier Ω, d x ≤ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ZeroBoundarySobolevPair p Ω (fun x => max (d x - ε) 0)
      (fun x => if ε < d x then gradient d x else 0) := by
  let K : Set (Space n) := closure Ω ∩ {x | ε ≤ d x}
  have hK : IsCompact K := hΩb.isCompact_closure.inter_right
    (isClosed_le continuous_const hd.continuous)
  have hKΩ : K ⊆ Ω := by
    intro x hx
    by_contra hxn
    have hxf : x ∈ frontier Ω := by
      rw [hΩ.frontier_eq]
      exact ⟨hx.1, hxn⟩
    have hb := hboundary x hxf
    have he : ε ≤ d x := hx.2
    linarith
  obtain ⟨f, hf⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hΩ hKΩ
  let χ : Space n → ℝ := fun x => Real.smoothTransition (f x)
  have hχcd : ContDiff ℝ ∞ χ :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).comp hf.1
  have hχc : HasCompactSupport χ := hf.2.1.comp_left
    (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)))
  have hχs : tsupport χ ⊆ Ω :=
    (tsupport_comp_subset (Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ))) f).trans hf.2.2.1
  have hχ0 (x : Space n) : 0 ≤ χ x := Real.smoothTransition.nonneg _
  have hχ1 (x : Space n) (hx : x ∈ K) : χ x = 1 :=
    Real.smoothTransition.one_of_one_le (hf.2.2.2 x hx)
  let ψ : Space n → ℝ := fun x => χ x * (d x - ε)
  have hψ : SmoothTest Ω ψ :=
    ⟨hχcd.mul (hd.sub contDiff_const), hχc.mul_right,
      tsupport_mul_subset_left.trans hχs⟩
  have hW := hψ.positivePart_zeroBoundarySobolevPair hp
  have hθeq : EqOn (fun x => max (ψ x) 0) (fun x => max (d x - ε) 0) Ω := by
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
      (fun x => if ε < d x then gradient d x else 0) Ω := by
    intro x hx
    by_cases hex : ε < d x
    · have hχx := hχ1 x ⟨subset_closure hx, hex.le⟩
      have hψpos : 0 < ψ x := by
        dsimp only [ψ]
        rw [hχx, one_mul]
        exact sub_pos.mpr hex
      have hN : Ω ∩ {y : Space n | ε < d y} ∈ 𝓝 x :=
        inter_mem (hΩ.mem_nhds hx) ((isOpen_lt continuous_const hd.continuous).mem_nhds hex)
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
  · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact hθeq hx
  · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    exact hGeq hx

theorem WeakPHarmonicPair.leOn_of_contDiff_boundary_order
    {n : ℕ} {p : ℝ} {Ω : Set (Space n)} {u v : Space n → ℝ}
    (hu : WeakPHarmonicPair p Ω u (gradient u))
    (hv : WeakPHarmonicPair p Ω v (gradient v))
    (huc : ContDiff ℝ ∞ u) (hvc : ContDiff ℝ ∞ v)
    (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ v x) :
    ∀ x ∈ Ω, u x ≤ v x := by
  have hD : LocalDomain Ω (Set.univ : Set (Space n)) :=
    ⟨hu.2.1, hΩb, subset_univ _⟩
  have hSu := sobolevPair_of_contDiffOn hu.1 isOpen_univ huc.contDiffOn hD
  have hSv := sobolevPair_of_contDiffOn hv.1 isOpen_univ hvc.contDiffOn hD
  have hgrad : gradient (fun x => u x - v x) = fun x => gradient u x - gradient v x :=
    funext (gradient_fun_sub (huc.differentiable (by simp)) (hvc.differentiable (by simp)))
  have heps (ε : ℝ) (hε : 0 < ε) : ∀ x ∈ Ω, u x ≤ v x + ε := by
    have hw := positivePart_sub_zeroBoundary_of_boundary_nonpos hu.1 hu.2.1 hΩb
      (huc.sub hvc) (fun x hx => sub_nonpos.mpr (hboundary x hx)) hε
    have hθ : (fun x => max ((fun y => u y - v y) x - ε) 0) =
        (fun x => max (u x - (v x + ε)) 0) := by
      funext x
      congr 1
      ring
    have hG : (fun x => if ε < (fun y => u y - v y) x then gradient (fun y => u y - v y) x else 0) =
        (fun x => if v x + ε < u x then gradient u x - gradient v x else 0) := by
      funext x
      rw [hgrad]
      have hh : ε < u x - v x ↔ v x + ε < u x := by constructor <;> intro h <;> linarith
      simp only [hh]
    rw [hθ, hG] at hw
    have hSvε : SobolevPair p Ω (fun x => v x + ε) (gradient v) := by
      have hs := hSv.add (sobolevPair_const hu.1 hΩb ε)
      exact hs.congr (Eventually.of_forall (fun x => by simp))
        (Eventually.of_forall (fun x => by simp))
    exact hu.leOn_of_zeroBoundary_positivePart (hv.add_const ε) hSu hSvε hn hΩb hw
      huc.continuous.continuousOn (hvc.continuous.add continuous_const).continuousOn
  intro x hx
  by_contra hnot
  have hpos : 0 < (u x - v x) / 2 := by linarith
  have hb := heps ((u x - v x) / 2) hpos x hx
  linarith

end BMCompactPDE
#print axioms BMCompactPDE.positivePart_sub_zeroBoundary_of_boundary_nonpos
#print axioms BMCompactPDE.WeakPHarmonicPair.leOn_of_contDiff_boundary_order
