import UpstreamMorreyRepresentative
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! Genuine every-point convergence from actual strong Sobolev approximation
above the dimension. Quantitative Morrey bounds apply to the actual continuous
differences. An AE anchor point is obtained after an actual Lp subsequence;
the subsequence criterion then recovers the WHOLE sequence at every point. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1200000 in
theorem exists_continuous_representative_and_pointwise_limit_of_strong_smooth_sobolev
    {n : ℕ} {p : ℝ} (hn : 1≤n) (hnp : (n:ℝ)<p)
    {u : Space n → ℝ} {g : Space n → Space n} (hu : SobolevPair p univ u g)
    {φ : ℕ → Space n → ℝ} (hφ : ∀ j,ContDiff ℝ ∞ (φ j)) (hc : ∀ j,HasCompactSupport (φ j))
    (hlimu : Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal p) volume) atTop (𝓝 0))
    (hlimg : Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0)) :
    ∃ v : Space n → ℝ,Continuous v ∧ u=ᵐ[volume] v ∧
      ∀ x : Space n,Tendsto (fun j=>φ j x) atTop (𝓝 (v x)) := by
  classical
  obtain ⟨A,hA⟩ := exists_actual_global_morrey_constant hn hnp
  obtain ⟨v,hvc,huv,-⟩ := hA u g hu
  have hvSob : SobolevPair p univ v g :=
    hu.congr (by simpa only [Measure.restrict_univ] using huv) EventuallyEq.rfl
  let d : ℕ → Space n → ℝ := fun j x=>φ j x-v x
  let G : ℕ → Space n → Space n := fun j x=>gradient (φ j) x-g x
  have hφSob (j : ℕ) : SobolevPair p univ (φ j) (gradient (φ j)) :=
    (show SmoothTest univ (φ j) from ⟨hφ j,hc j,subset_univ _⟩).sobolevPair hu.1
  have hinc (j : ℕ) (x y : Space n) :
      dist (d j x) (d j y)≤(A:ℝ)*(eLpNorm (G j) (ENNReal.ofReal p) volume).toReal*dist x y^(1-(n:ℝ)/p) := by
    have hdSob : SobolevPair p univ (d j) (G j) := by
      simpa only [d,G,neg_one_smul,sub_eq_add_neg,Pi.add_apply,Pi.neg_apply] using! (hφSob j).add (hvSob.smul (-1))
    obtain ⟨w,hw,hdw,hbound⟩ := hA (d j) (G j) hdSob
    have heq : EqOn (d j) w univ := Measure.eqOn_open_of_ae_eq (μ:=volume) (by simpa only [Measure.restrict_univ] using hdw) isOpen_univ
      ((hφ j).continuous.sub hvc).continuousOn hw.continuousOn
    simpa only [heq (mem_univ x),heq (mem_univ y)] using hbound x y
  have hgradreal : Tendsto (fun j=>(eLpNorm (G j) (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.toReal_zero,G] using
      (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞)≠(∞:ℝ≥0∞))).tendsto.comp hlimg
  refine ⟨v,hvc,huv,?_⟩
  intro x
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hp0 : 0<p := zero_lt_one.trans hu.1
  have hum : MemLp u (ENNReal.ofReal p) volume := by simpa only [Measure.restrict_univ] using hu.2.1
  have hmeas (j : ℕ) : AEStronglyMeasurable (φ (ns j)) volume := (hφ (ns j)).continuous.aestronglyMeasurable
  have hm := tendstoInMeasure_of_tendsto_eLpNorm (ENNReal.ofReal_ne_zero_iff.mpr hp0)
    hmeas hum.1 (hlimu.comp hns)
  obtain ⟨σ,hσ,hσlim⟩ := hm.exists_seq_tendsto_ae
  have hAE : ∀ᵐ y ∂volume,Tendsto (fun j=>φ (ns (σ j)) y) atTop (𝓝 (v y)) := by
    filter_upwards [hσlim,huv] with y hy hyv
    rwa [hyv] at hy
  obtain ⟨y,hy⟩ := hAE.exists
  refine ⟨σ,?_⟩
  have hyd : Tendsto (fun j=>d (ns (σ j)) y) atTop (𝓝 0) := by
    simpa only [d,sub_self] using hy.sub_const (v y)
  have hN := hgradreal.comp (hns.comp hσ.tendsto_atTop)
  have hboundlim : Tendsto (fun j=>(A:ℝ)*(eLpNorm (G (ns (σ j))) (ENNReal.ofReal p) volume).toReal*
      dist x y^(1-(n:ℝ)/p)+‖d (ns (σ j)) y‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,zero_mul,add_zero,norm_zero] using
      ((hN.const_mul (A:ℝ)).mul_const (dist x y^(1-(n:ℝ)/p))).add hyd.norm
  have hnorm : Tendsto (fun j=>‖d (ns (σ j)) x‖) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hboundlim (fun _=>norm_nonneg _)
    intro j
    have hh : ‖d (ns (σ j)) x‖≤dist (d (ns (σ j)) x) (d (ns (σ j)) y)+‖d (ns (σ j)) y‖ := by
      simpa only [dist_eq_norm] using norm_le_norm_sub_add (d (ns (σ j)) x) (d (ns (σ j)) y)
    exact hh.trans (add_le_add (hinc _ x y) le_rfl)
  have hd : Tendsto (fun j=>d (ns (σ j)) x) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa only [d,sub_add_cancel,zero_add] using hd.add_const (v x)

end BMCompactPDE
#print axioms BMCompactPDE.exists_continuous_representative_and_pointwise_limit_of_strong_smooth_sobolev
