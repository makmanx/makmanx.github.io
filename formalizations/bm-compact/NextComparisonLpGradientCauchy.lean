import NextComparisonLocalLpStability
import UpstreamGreenLocalGradientBound
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Cauchy

/-! Actual local Lp gradient Cauchy control from a scalar uniform limit of
genuine homogeneous weak solutions. The gradient norm ceilings and energy
estimate are derived from the scalar ceiling and actual PDE. No gradient
closeness, gradient convergence, limit gradient or limit PDE is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem green_cauchy_integral_norm_power
    {n : ℕ} {p : ℝ} {μ : Measure (Space n)} {g : Space n → Space n}
    (hp : 1<p) (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫ x,‖g x‖^p ∂μ)=(eLpNorm g (ENNReal.ofReal p) μ).toReal^p := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have ht := BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp) (hg.toLp g)
  rw [Lp.norm_toLp] at ht
  have he := integral_congr_ae (hg.coeFn_toLp.fun_comp (fun v => ‖v‖^p))
  exact (ht.trans he).symm

set_option maxHeartbeats 1200000 in
/-- Strong scalar Lp convergence and a common scalar ceiling force the actual
weak-gradient representatives to be Cauchy in local Lp. The displayed Fact
instance is derived solely from p>=2 and only equips the actual Lp space
with its native normed metric; it is not an additional analytic premise. -/
theorem local_gradient_cauchySeq_of_strong_scalar_Lp_limit
    {n : ℕ} {p : ℝ} (hp : 2≤p) {U D : Set (Space n)}
    (hU : IsOpen U) (hD : LocalDomain D U)
    {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n} {f : Space n → ℝ}
    (hu : ∀ j,WeakPHarmonicPair p U (u j) (g j))
    {B : ℝ} (hB : 0≤B) (hbound : ∀ j,∀ x∈U,|u j x|≤B)
    (huMem : ∀ j,MemLp (u j) (ENNReal.ofReal p) (volume.restrict U))
    (hfMem : MemLp f (ENNReal.ofReal p) (volume.restrict U))
    (hlim : Tendsto (fun j=>eLpNorm (u j-f) (ENNReal.ofReal p) (volume.restrict U)) atTop (𝓝 0)) :
    letI : Fact (1≤ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr ((by norm_num : (1:ℝ)≤2).trans hp)⟩
    CauchySeq (fun j => ((hu j).2.2.1 D hD).2.2.1.toLp (g j)) := by
  letI : Fact (1≤ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr ((by norm_num : (1:ℝ)≤2).trans hp)⟩
  have hp1 : 1<p := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) hp
  have hp0 : 0<p := zero_lt_one.trans hp1
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨r,hr,hthick⟩ := hK.exists_cthickening_subset_open hU hD.2.2
  let V : Set (Space n) := thickening r (closure D)
  have hV : LocalDomain V U := by
    refine ⟨isOpen_thickening,hK.isBounded.thickening,?_⟩
    exact (closure_thickening_subset_cthickening r (closure D)).trans hthick
  have hDV : LocalDomain D V := ⟨hD.1,hD.2.1,self_subset_thickening hr (closure D)⟩
  have hVU : V⊆U := subset_closure.trans hV.2.2
  obtain ⟨Cs,hCs,hEst⟩ := exists_local_gradient_stability_constant_of_scalar_Lp_gap hp hV.1 hDV
  obtain ⟨Cg,hCg,hGrad⟩ := exists_local_gradient_norm_bound_of_scalar_bound hp1 hU hV
  let L : ℝ := Cs*((2*Cg)*B)^(p-1)
  have hL : 0≤L := mul_nonneg hCs (Real.rpow_nonneg (by positivity) _)
  have hScalarCauchy := ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' u huMem f hfMem).mpr hlim).cauchySeq
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hεp : 0<ε^p := Real.rpow_pos_of_pos hε _
  let δ : ℝ := ε^p/(2*(1+L))
  have hden : 0<2*(1+L) := by positivity
  have hδ : 0<δ := div_pos hεp hden
  have hsmall : L*δ<ε^p := by
    dsimp only [δ]
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ hden).mpr
    nlinarith only [hεp,mul_nonneg hL hεp.le]
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hScalarCauchy δ hδ
  refine ⟨N,?_⟩
  intro j hj k hk
  have hgapU : (eLpNorm (u j-u k) (ENNReal.ofReal p) (volume.restrict U)).toReal<δ := by
    have hd := hN j hj k hk
    rw [Lp.dist_edist,Lp.edist_toLp_toLp] at hd
    exact hd
  have hgapV : (eLpNorm (u j-u k) (ENNReal.ofReal p) (volume.restrict V)).toReal≤
      (eLpNorm (u j-u k) (ENNReal.ofReal p) (volume.restrict U)).toReal :=
    ENNReal.toReal_mono ((huMem j).sub (huMem k)).eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hVU))
  have hNg := hGrad _ _ (hu j) B hB (hbound j)
  have hNh := hGrad _ _ (hu k) B hB (hbound k)
  obtain ⟨-,hE⟩ := hEst 0 (u j) (u k) (g j) (g k)
    ((hu j).source_zero.mono_actual hVU hV.1) ((hu k).source_zero.mono_actual hVU hV.1)
    ((hu j).2.2.1 V hV) ((hu k).2.2.1 V hV)
  have hsum : (eLpNorm (g j) (ENNReal.ofReal p) (volume.restrict V)).toReal+
      (eLpNorm (g k) (ENNReal.ofReal p) (volume.restrict V)).toReal≤(2*Cg)*B := by
    linarith only [hNg,hNh]
  have hpow := Real.rpow_le_rpow (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    hsum (by linarith : 0≤p-1)
  have hEstSmall : (∫ x in D,‖g j x-g k x‖^p)≤L*δ := by
    calc
      _≤Cs*(eLpNorm (u j-u k) (ENNReal.ofReal p) (volume.restrict V)).toReal*
          ((eLpNorm (g j) (ENNReal.ofReal p) (volume.restrict V)).toReal+
          (eLpNorm (g k) (ENNReal.ofReal p) (volume.restrict V)).toReal)^(p-1) := hE
      _≤Cs*δ*((2*Cg)*B)^(p-1) := mul_le_mul
        (mul_le_mul_of_nonneg_left (hgapV.trans hgapU.le) hCs) hpow
        (Real.rpow_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) _)
        (mul_nonneg hCs hδ.le)
      _=L*δ := by dsimp only [L];ring
  have hEc : (∫ x in D,‖g j x-g k x‖^p)<ε^p := hEstSmall.trans_lt hsmall
  have hgj := ((hu j).2.2.1 D hD).2.2.1
  have hgk := ((hu k).2.2.1 D hD).2.2.1
  have hnorm : (eLpNorm (g j-g k) (ENNReal.ofReal p) (volume.restrict D)).toReal^p<ε^p := by
    have he := (green_cauchy_integral_norm_power hp1 (hgj.sub hgk)).symm
    have he' : (eLpNorm (g j-g k) (ENNReal.ofReal p) (volume.restrict D)).toReal^p=
        ∫ x in D,‖g j x-g k x‖^p := by
      simpa only [Pi.sub_apply] using he
    rw [he']
    exact hEc
  change dist (hgj.toLp (g j)) (hgk.toLp (g k))<ε
  rw [Lp.dist_edist,Lp.edist_toLp_toLp]
  exact (Real.rpow_lt_rpow_iff ENNReal.toReal_nonneg hε.le hp0).mp hnorm

end BMCompactPDE
#print axioms BMCompactPDE.local_gradient_cauchySeq_of_strong_scalar_Lp_limit
