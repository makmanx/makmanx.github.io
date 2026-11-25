import RootWeakMollification
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Topology.UniformSpace.HeineCantor

/-! A continuous actual weak gradient gives classical C1 regularity.
This bridge assumes continuity of the weak field explicitly; it does not
construct that continuity from the nonlinear PDE. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric ContinuousLinearMap
open scoped Topology ENNReal Convolution ContDiff
namespace BMCompactPDE

private theorem root_tendstoUniformly_bump_convolution
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {g : Space n → F} (hg : Continuous g) (hgc : HasCompactSupport g)
    {φ : ℕ → ContDiffBump (0 : Space n)}
    (hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0)) :
    TendstoUniformly (fun j => (φ j).normed volume ⋆[lsmul ℝ ℝ,volume] g) g atTop := by
  have huc := hgc.uniformContinuous_of_continuous hg
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp huc (ε/2) (by linarith)
  have hsmall : ∀ᶠ j in atTop,(φ j).rOut<δ := (tendsto_order.mp hφ).2 δ hδ
  filter_upwards [hsmall] with j hj
  intro x
  have hbound : dist (((φ j).normed volume ⋆[lsmul ℝ ℝ,volume] g) x) (g x)≤ε/2 :=
    (φ j).dist_normed_convolution_le hg.aestronglyMeasurable (by
      intro y hy
      exact (hclose (lt_trans (mem_ball.mp hy) hj)).le)
  have hd : dist (((φ j).normed volume ⋆[lsmul ℝ ℝ,volume] g) x) (g x)<ε :=
    hbound.trans_lt (half_lt_self hε)
  simpa only [dist_comm] using hd

set_option maxHeartbeats 1000000 in
theorem SobolevPair.contDiff_one_of_continuous_gradient_univ
    {n : ℕ} {p : ℝ} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : SobolevPair p univ u g) (huc : Continuous u)
    (hgc : Continuous g) (hgcompact : HasCompactSupport g) :
    ContDiff ℝ 1 u := by
  let φ : ℕ → ContDiffBump (0 : Space n) := fun j =>
    ⟨1/((j:ℝ)+2),2/((j:ℝ)+2),by positivity,by gcongr;norm_num⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) := by
    change Tendsto (fun j : ℕ => 2/((j:ℝ)+2)) atTop (𝓝 0)
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  let U : ℕ → Space n → ℝ := fun j => (φ j).normed volume ⋆[lsmul ℝ ℝ,volume] u
  let G : ℕ → Space n → Space n := fun j => (φ j).normed volume ⋆[lsmul ℝ ℝ,volume] g
  have hU (j : ℕ) : ContDiff ℝ 1 (U j) :=
    (φ j).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      (φ j).contDiff_normed huc.locallyIntegrable
  have hgrad (j : ℕ) : gradient (U j)=G j :=
    hu.gradient_convolution_eq (φ j).contDiff_normed (φ j).hasCompactSupport_normed
  have hDU (j : ℕ) (x : Space n) : HasFDerivAt (U j) (toDual ℝ (Space n) (G j x)) x := by
    rw [←congrFun (hgrad j) x,toDual_gradient]
    exact ((hU j).differentiable one_ne_zero x).hasFDerivAt
  have hG : TendstoUniformly G g atTop := root_tendstoUniformly_bump_convolution hgc hgcompact hφ
  have hDG : TendstoUniformly (fun j x => toDual ℝ (Space n) (G j x))
      (fun x => toDual ℝ (Space n) (g x)) atTop := by
    rw [Metric.tendstoUniformly_iff] at hG ⊢
    intro ε hε
    filter_upwards [hG ε hε] with j hj
    intro x
    exact ((toDual ℝ (Space n)).isometry.dist_eq _ _).trans_lt (hj x)
  have hder (x : Space n) : HasFDerivAt u (toDual ℝ (Space n) (g x)) x :=
    hasFDerivAt_of_tendstoUniformly hDG hDU
      (fun x => ContDiffBump.convolution_tendsto_right_of_continuous hφ huc x) x
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hder x).differentiableAt,?_⟩
  have he : fderiv ℝ u=(fun x => toDual ℝ (Space n) (g x)) := funext (fun x => (hder x).fderiv)
  rw [he]
  exact (toDual ℝ (Space n)).continuous.comp hgc

end BMCompactPDE
#print axioms BMCompactPDE.SobolevPair.contDiff_one_of_continuous_gradient_univ
