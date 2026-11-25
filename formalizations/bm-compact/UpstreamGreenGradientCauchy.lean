import UpstreamGreenScalarStability
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
/-- Scalar uniform convergence and a common scalar ceiling force the actual
weak-gradient representatives to be Cauchy in local Lp. The displayed Fact
instance is derived solely from p>=2 and only equips the actual Lp space
with its native normed metric; it is not an additional analytic premise. -/
theorem local_gradient_cauchySeq_of_uniform_scalar_limit
    {n : ℕ} {p : ℝ} (hp : 2≤p) {U D : Set (Space n)}
    (hU : IsOpen U) (hD : LocalDomain D U)
    {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n} {f : Space n → ℝ}
    (hu : ∀ j,WeakPHarmonicPair p U (u j) (g j))
    {B : ℝ} (hB : 0≤B) (hbound : ∀ j,∀ x∈U,|u j x|≤B)
    (hlim : TendstoUniformlyOn u f atTop U) :
    letI : Fact (1≤ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr ((by norm_num : (1:ℝ)≤2).trans hp)⟩
    CauchySeq (fun j => ((hu j).2.2.1 D hD).2.2.1.toLp (g j)) := by
  letI : Fact (1≤ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr ((by norm_num : (1:ℝ)≤2).trans hp)⟩
  have hp1 : 1<p := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) hp
  have hp0 : 0<p := zero_lt_one.trans hp1
  obtain ⟨C,hC,hEst⟩ := exists_local_gradient_stability_of_scalar_bounds hp hU hD
  let L : ℝ := C*B^(p-1)
  have hL : 0≤L := mul_nonneg hC (Real.rpow_nonneg hB _)
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
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    ((Metric.tendstoUniformlyOn_iff.mp hlim) (δ/2) (half_pos hδ))
  refine ⟨N,?_⟩
  intro j hj k hk
  have hgap : ∀ x∈U,|u j x-u k x|≤δ := by
    intro x hx
    have hjx : |u j x-f x|<δ/2 := by
      simpa only [Real.dist_eq,abs_sub_comm] using hN j hj x hx
    have hkx : |f x-u k x|<δ/2 := by
      simpa only [Real.dist_eq] using hN k hk x hx
    exact (abs_sub_le (u j x) (f x) (u k x)).trans (by linarith only [hjx,hkx])
  obtain ⟨-,hE⟩ := hEst (u j) (u k) (g j) (g k) (hu j) (hu k)
    B δ hB hδ.le (hbound j) (hbound k) hgap
  have hEc : (∫ x in D,‖g j x-g k x‖^p)<ε^p := by
    have he : C*δ*B^(p-1)=L*δ := by dsimp only [L];ring
    exact (hE.trans_eq he).trans_lt hsmall
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
#print axioms BMCompactPDE.local_gradient_cauchySeq_of_uniform_scalar_limit
