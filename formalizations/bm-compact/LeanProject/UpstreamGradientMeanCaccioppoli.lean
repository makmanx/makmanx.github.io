import UpstreamGradientDiscreteEquation
import UpstreamGradientWeightedEllipticity
import GradientRegularizedCaccioppoli

/-! Genuine weighted Caccioppoli energy for actual regularized weak solutions,
using the SAME averaged coefficient weight on both sides. The compact W0 test
comes from the actual Sobolev pair. No derivative equation, gradient bound,
energy inequality, or smoothness of either weak solution is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 400000 in
set_option diagnostics true in
private theorem upstream_integrable_mean_weighted_square
    {n : ℕ} {p ε : ℝ} {μ : Measure (Space n)} [IsFiniteMeasure μ]
    (hp : 2≤p) (hε : ε≠0) {g h : Space n → Space n} {z : Space n → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) μ) (hh : MemLp h (ENNReal.ofReal p) μ)
    (hz : MemLp z (ENNReal.ofReal p) μ) :
    Integrable (fun x => regularizedMeanWeight p ε (g x) (h x)*‖z x‖^2) μ := by
  have hraw := integrable_regularized_weighted_square (n:=n) (p:=p) (ε:=ε)
    (μ:=μ) (g:=g) (h:=h) (z:=z) hp hg hh hz
  have hbase : Integrable (fun x => (ε^2+(max ‖g x‖ ‖h x‖)^2)^((p-2)/2)*‖z x‖^2) μ := by
    exact hraw
  have hprod : AEStronglyMeasurable (fun x => (g x,h x)) μ := hg.1.prodMk hh.1
  have hcont := continuous_regularizedMeanWeight (E:=Space n) p hε
  have hLamRaw := hcont.comp_aestronglyMeasurable hprod
  have hlam : AEStronglyMeasurable (fun x => regularizedMeanWeight p ε (g x) (h x)) μ := by
    simpa only [Function.comp_def] using! hLamRaw
  have hz2 : AEStronglyMeasurable (fun x => ‖z x‖^2) μ := hz.1.norm.pow 2
  have hm : AEStronglyMeasurable (fun x => regularizedMeanWeight p ε (g x) (h x)*‖z x‖^2) μ :=
    hlam.mul hz2
  apply hbase.mono' hm
  apply Eventually.of_forall
  intro x
  obtain ⟨hpos,hupper,-,-⟩ := regularizedMeanJacobian_weighted_ellipticity (E:=Space n) hp hε (g x) (h x)
  have hnonneg : 0≤regularizedMeanWeight p ε (g x) (h x)*‖z x‖^2 :=
    mul_nonneg hpos.le (sq_nonneg ‖z x‖)
  rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
  exact mul_le_mul_of_nonneg_right hupper (sq_nonneg ‖z x‖)

private theorem upstream_matrix_cutoff_error
    {n : ℕ} {C lam η z : ℝ} (hC : 0≤C) (hlam : 0≤lam)
    (A : Space n →L[ℝ] Space n) (hA : ‖A‖≤C*lam) (v b : Space n) :
    -z*inner ℝ (A v) ((2*η) • b)≤
      (1/2:ℝ)*(η^2*lam*‖v‖^2)+2*C^2*(lam* |z|^2*‖b‖^2) := by
  have hinner : |inner ℝ (A v) b|≤C*lam*‖v‖*‖b‖ :=
    (abs_real_inner_le_norm (A v) b).trans
      (mul_le_mul_of_nonneg_right ((A.le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hA (norm_nonneg v))) (norm_nonneg b))
  have hfirst : -z*inner ℝ (A v) ((2*η) • b)≤
      2* |η| * |z| * |inner ℝ (A v) b| := by
    rw [inner_smul_right]
    calc
      _≤|-z*((2*η)*inner ℝ (A v) b)| := le_abs_self _
      _=_ := by simp only [abs_mul,abs_neg,abs_of_nonneg (show (0:ℝ)≤2 by norm_num)];ring
  have hsecond := mul_le_mul_of_nonneg_left hinner
    (by positivity : 0≤2* |η| * |z|)
  have hYoung : 2* |η| * |z| * (C*lam*‖v‖*‖b‖)≤
      (1/2:ℝ)*(η^2*lam*‖v‖^2)+2*C^2*(lam* |z|^2*‖b‖^2) := by
    have hs := mul_nonneg hlam (sq_nonneg (|η| * ‖v‖-2*C* |z| * ‖b‖))
    simp only [sub_sq,mul_pow,sq_abs] at hs
    rw [sq_abs]
    nlinarith only [hs]
  exact hfirst.trans (hsecond.trans hYoung)

set_option maxHeartbeats 1600000 in
/-- Two actual fixed-source regularized weak solutions satisfy the genuine
common-weight quadratic Caccioppoli inequality. In particular this applies to
an actual solution and its translate, furnishing the finite-difference Moser
energy foundation. The constant 4*(p-1)^2 is independent of epsilon. -/
theorem GlobalWeakRegularizedSourcePair.caccioppoli_mean_weighted_difference
    {n : ℕ} {p ε c : ℝ} {Ω : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : GlobalWeakRegularizedSourcePair p ε c Ω u g)
    (hv : GlobalWeakRegularizedSourcePair p ε c Ω v h)
    (hp : 2≤p) (hε : ε≠0) (hΩb : Bornology.IsBounded Ω)
    {η : Space n → ℝ} (hη : SmoothTest Ω η) :
    Integrable (fun x => η x^2*regularizedMeanWeight p ε (g x) (h x)*‖g x-h x‖^2)
      (volume.restrict Ω) ∧
    Integrable (fun x => regularizedMeanWeight p ε (g x) (h x)*|u x-v x|^2*‖gradient η x‖^2)
      (volume.restrict Ω) ∧
    (∫ x in Ω,η x^2*regularizedMeanWeight p ε (g x) (h x)*‖g x-h x‖^2)≤
      4*(p-1)^2*(∫ x in Ω,regularizedMeanWeight p ε (g x) (h x)*
        |u x-v x|^2*‖gradient η x‖^2) := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  let W : Space n → ℝ := fun x => regularizedMeanWeight p ε (g x) (h x)
  let L : Space n → ℝ := fun x => η x^2*W x*‖g x-h x‖^2
  let R : Space n → ℝ := fun x => W x* |u x-v x|^2*‖gradient η x‖^2
  let χ : Space n → ℝ := fun x => η x*η x
  have hχ : SmoothTest Ω χ :=
    ⟨hη.1.mul hη.1,hη.2.1.mul_right,tsupport_mul_subset_left.trans hη.2.2⟩
  have hgrad (x : Space n) : gradient χ x=(2*η x) • gradient η x := by
    rw [gradient_fun_mul_actual (hη.1.differentiable (by simp)).differentiableAt
      (hη.1.differentiable (by simp)).differentiableAt]
    module
  have hg := hu.2.2.1.2.2.1
  have hh := hv.2.2.1.2.2.1
  have hbase := upstream_integrable_mean_weighted_square hp hε hg hh
    (hu.2.2.1.2.1.sub hv.2.2.1.2.1)
  have hgradtop : MemLp (gradient η) (∞:ℝ≥0∞) (volume.restrict Ω) :=
    (continuous_gradient_of_contDiff_one (hη.1.of_le (by simp))).memLp_top_of_hasCompactSupport
      (BMCompactCapacityV2.gradient_hasCompactSupport hη.2.1) _
  have hgradpow : MemLp (fun x => ‖gradient η x‖^2) (∞:ℝ≥0∞) (volume.restrict Ω) := by
    simpa only [pow_two] using hgradtop.norm.mul' hgradtop.norm
  have hRI : Integrable R (volume.restrict Ω) := by
    simpa only [R,W,Pi.mul_apply,Real.norm_eq_abs,Pi.sub_apply,mul_comm] using!
      hbase.mul_of_top_right hgradpow
  have hLI : Integrable L (volume.restrict Ω) := by
    have hb := upstream_integrable_mean_weighted_square hp hε hg hh (hg.sub hh).norm
    have hηtop := hη.1.continuous.memLp_top_of_hasCompactSupport hη.2.1 (volume.restrict Ω)
    have hηpow : MemLp (fun x => η x^2) (∞:ℝ≥0∞) (volume.restrict Ω) := by
      simpa only [pow_two] using hηtop.mul' hηtop
    convert! hb.mul_of_top_right hηpow using 1
    funext x
    simp only [L,W,Pi.mul_apply,Real.norm_eq_abs,Pi.sub_apply,abs_norm]
    ring
  refine ⟨hLI,hRI,?_⟩
  obtain ⟨hA,hB,he⟩ := hu.local_flux_difference_identity hv hΩb hχ
  have hco := integral_mono hLI hA (fun x => by
    have hl := (regularizedMeanJacobian_weighted_ellipticity (E:=Space n) hp hε (g x) (h x)).2.2.2 (g x-h x)
    rw [regularizedMeanJacobian_apply_sub p hε] at hl
    have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg (η x))
    simpa only [L,W,χ,pow_two,mul_assoc] using hm)
  have hYoung := integral_mono hB.neg
    ((hLI.const_mul (1/2:ℝ)).add (hRI.const_mul (2*(p-1)^2))) (fun x => by
      obtain ⟨hpos,-,hOp,-⟩ := regularizedMeanJacobian_weighted_ellipticity (E:=Space n) hp hε (g x) (h x)
      have hy := upstream_matrix_cutoff_error (by linarith : 0≤p-1) hpos.le
        (regularizedMeanJacobian p ε (g x) (h x)) hOp (g x-h x) (gradient η x)
        (η:=η x) (z:=u x-v x)
      rw [regularizedMeanJacobian_apply_sub p hε] at hy
      simp only [Pi.neg_apply,Pi.add_apply]
      rw [hgrad]
      simpa only [L,R,W,Pi.neg_apply,Pi.add_apply,neg_mul,mul_assoc] using hy)
  change (∫ x in Ω,L x)≤4*(p-1)^2*(∫ x in Ω,R x)
  change (∫ x in Ω,-((u x-v x)*inner ℝ
    ((ε^2+‖g x‖^2)^((p-2)/2) • g x-(ε^2+‖h x‖^2)^((p-2)/2) • h x)
    (gradient χ x)))≤∫ x in Ω,(1/2:ℝ)*L x+(2*(p-1)^2)*R x at hYoung
  rw [integral_neg,integral_add (hLI.const_mul (1/2:ℝ)) (hRI.const_mul (2*(p-1)^2)),
    integral_const_mul,integral_const_mul] at hYoung
  nlinarith only [hco,hYoung,he]

end BMCompactPDE
#print axioms BMCompactPDE.GlobalWeakRegularizedSourcePair.caccioppoli_mean_weighted_difference
