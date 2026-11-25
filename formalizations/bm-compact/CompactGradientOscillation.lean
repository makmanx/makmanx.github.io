import RootClassicalGradientIdentification
import BMCompactChecked
import RootW0Linear
import RootSobolevLocalization
import LpDominatedLimit
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Connected.LocallyConnected

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Bornology InnerProductSpace
open scoped Topology ENNReal ContDiff BoundedContinuousFunction
namespace BMCompactPDE

/-- Vanishing Sobolev gradients and equicontinuity on a compact window give
arbitrarily small scalar oscillation on every connected probe inside it. -/
theorem exists_subsequence_small_oscillation_on_connected {n : ℕ} {p : ℝ} (hp : 1 < p)
    {Q D C U : Set (Space n)} (hQ : IsPreconnected Q) (hQD : Q ⊆ D)
    (hD : IsOpen D) (hDC : D ⊆ C) (hC : IsCompact C) (hCU : C ⊆ U)
    {k : ℕ → Space n → ℝ} {H : ℕ → Space n → Space n}
    (hSob : ∀ j, SobolevPair p U (k j) (H j))
    (heq : Equicontinuous (fun (j : ℕ) (x : C) => k j x.val))
    {B : ℝ} (hB : ∀ j x, x ∈ C → |k j x| ≤ B)
    (hgrad : Tendsto (fun j => (eLpNorm (H j) (ENNReal.ofReal p) (volume.restrict U)).toReal)
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ j ≥ N, ∀ x ∈ Q, ∀ y ∈ Q, |k j x-k j y| < ε := by
  classical
  let _ : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let v : ℕ → C →ᵇ ℝ := fun j => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => k j x.val, heq.continuous j⟩
  let A := range v
  have heA : Equicontinuous ((↑) : A → C → ℝ) := by
    let idx : A → ℕ := fun f => f.property.choose
    have hi (f : A) : v (idx f) = f.val := f.property.choose_spec
    convert heq.comp idx using 1
    funext f x
    change f.val x = v (idx f) x
    rw [hi]
  have hcA := BoundedContinuousFunction.arzela_ascoli (Icc (-B) B) isCompact_Icc A
    (fun f x hf => by obtain ⟨j,rfl⟩ := hf; exact abs_le.mp (hB j x x.property)) heA
  obtain ⟨f,_,s,hsm,hlim⟩ := hcA.tendsto_subseq (fun j => subset_closure (mem_range_self j))
  let F : Space n → ℝ := fun x => if hx : x ∈ C then f ⟨x,hx⟩ else 0
  have hFc (x : C) : F x.val = f x := by simp [F,x.property]
  have hcont : ContinuousOn F D := by
    apply ContinuousOn.mono (s := C) _ hDC
    rw [continuousOn_iff_continuous_domRestrict]
    exact f.continuous.congr (fun x => (hFc x).symm)
  have hbound (j : ℕ) (x : Space n) (hx : x ∈ C) :
      |k (s j) x - F x| ≤ dist (v (s j)) f := by
    rw [show F x = f ⟨x,hx⟩ from hFc ⟨x,hx⟩,← Real.dist_eq]
    exact BoundedContinuousFunction.dist_coe_le_dist (f:=v (s j)) (g:=f) (⟨x,hx⟩ : C)
  have hdist : Tendsto (fun j => dist (v (s j)) f) atTop (𝓝 0) := tendsto_iff_dist_tendsto_zero.mp hlim
  have hpnt (x : Space n) (hx : x ∈ C) : Tendsto (fun j => k (s j) x) atTop (𝓝 (F x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdist (fun _ => dist_nonneg)
      (fun j => by simpa only [Real.dist_eq] using hbound j x hx)
  let μ := (volume : Measure (Space n)).restrict D
  let _ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (hC.isBounded.subset hDC).measure_lt_top.ne
  have hS (j : ℕ) := (hSob (s j)).mono_actual (hDC.trans hCU)
  have hpt : ∀ᵐ x ∂μ, Tendsto (fun j => k (s j) x) atTop (𝓝 (F x)) := by
    filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    exact hpnt x (hDC hx)
  have hme := aestronglyMeasurable_of_tendsto_ae atTop (fun j => (hS j).2.1.1) hpt
  have hbF (x : Space n) (hx : x ∈ C) : ‖F x‖ ≤ B :=
    le_of_tendsto' (hpnt x hx).norm (fun j => hB _ x hx)
  have hLp : MemLp F (ENNReal.ofReal p) μ := (memLp_const B).of_le hme (by
    filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
    exact (hbF x (hDC hx)).trans (le_abs_self B))
  have hul : Tendsto (fun j => eLpNorm (k (s j)-F) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_zero_of_dominated (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp))
      ENNReal.ofReal_ne_top (fun j => (hS j).2.1.1.sub hme) (memLp_const (2*B))
    · intro j
      filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
      have h₁ := hB (s j) x (hDC hx)
      have h₂ := hbF x (hDC hx)
      have h₃ : ‖k (s j) x‖ ≤ B := h₁
      have h₄ : ‖k (s j) x‖+‖F x‖ ≤ 2*B := by linarith only [h₃,h₂]
      exact (norm_sub_le _ _).trans (h₄.trans (le_abs_self _))
    · filter_upwards [hpt] with x hx
      simpa only [Pi.sub_apply,sub_self] using hx.sub_const (F x)
  have hUg := (ENNReal.tendsto_toReal_zero_iff (fun j => (hSob j).2.2.1.2.ne)).mp hgrad
  have hgl : Tendsto (fun j => eLpNorm (fun x => H (s j) x-(0:Space n)) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
    simp only [sub_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hUg.comp hsm.tendsto_atTop)
      (fun _ => bot_le) (fun j => eLpNorm_mono_measure _ (Measure.restrict_mono (hDC.trans hCU) le_rfl))
  have hS0 := sobolevPair_of_eLpNorm_limits hp hS hLp (MemLp.zero) hul hgl
  have hc1 := hS0.contDiffOn_one_of_continuous_gradient hD hcont continuousOn_const
  have hegrad := hS0.2.2.2.eqOn_classical_gradient_of_continuous hD hc1 continuousOn_const
  have heF (x : Space n) (hx : x ∈ Q) (y : Space n) (hy : y ∈ Q) : F x = F y := by
    let V := connectedComponentIn D x
    have ho : IsOpen V := hD.connectedComponentIn
    have hsV : V ⊆ D := connectedComponentIn_subset D x
    apply ho.is_const_of_fderiv_eq_zero isPreconnected_connectedComponentIn
      ((hc1.differentiableOn (by simp)).mono hsV) _ (mem_connectedComponentIn (hQD hx))
      (hQ.subset_connectedComponentIn hx hQD hy)
    intro z hz
    rw [← toDual_gradient,← hegrad (hsV hz)]
    exact map_zero _
  intro ε hε N
  obtain ⟨j,hj,hl⟩ := ((hsm.tendsto_atTop.eventually (eventually_ge_atTop N)).and
    (hdist.eventually_lt_const (half_pos hε))).exists
  refine ⟨s j,hj,?_⟩
  intro x hx y hy
  have h₁ := (hbound j x (hDC (hQD hx))).trans_lt hl
  have h₂ := (hbound j y (hDC (hQD hy))).trans_lt hl
  rw [heF x hx y hy] at h₁
  exact abs_lt.mpr ⟨by linarith only [(abs_lt.mp h₁).1,(abs_lt.mp h₂).2],
    by linarith only [(abs_lt.mp h₁).2,(abs_lt.mp h₂).1]⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_subsequence_small_oscillation_on_connected
