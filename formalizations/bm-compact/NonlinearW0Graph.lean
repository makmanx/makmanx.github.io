import RootW0Linear
import RootPoincare
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.Sequences

/-! The genuine all-p W0 graph, closed gradient range and quantitative inverse bound.
No solution, minimizer or closed-range conclusion is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

abbrev ScalarLp (p : ℝ) (n : ℕ) (Ω : Set (Space n)) := Lp ℝ (ENNReal.ofReal p) (volume.restrict Ω)
abbrev VectorLp (p : ℝ) (n : ℕ) (Ω : Set (Space n)) := Lp (Space n) (ENNReal.ofReal p) (volume.restrict Ω)

variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

def w0LpGraph (hp : 1<p) (n : ℕ) (Ω : Set (Space n)) :
    Submodule ℝ (ScalarLp p n Ω × VectorLp p n Ω) where
  carrier := {w | ZeroBoundarySobolevPair p Ω (w.1 : Space n → ℝ) (w.2 : Space n → Space n)}
  zero_mem' := by
    exact (zeroBoundarySobolevPair_zero (n := n) (p := p) hp Ω).congr
      (Lp.coeFn_zero ℝ (ENNReal.ofReal p) (volume.restrict Ω)).symm
      (Lp.coeFn_zero (Space n) (ENNReal.ofReal p) (volume.restrict Ω)).symm
  add_mem' := by
    intro x y hx hy
    exact (ZeroBoundarySobolevPair.add_actual hx hy).congr (Lp.coeFn_add x.1 y.1).symm (Lp.coeFn_add x.2 y.2).symm
  smul_mem' := by
    intro c x hx
    exact (ZeroBoundarySobolevPair.smul_actual hx c).congr (Lp.coeFn_smul c x.1).symm (Lp.coeFn_smul c x.2).symm

theorem w0LpGraph_mem_iff (hp : 1<p) {n : ℕ} {Ω : Set (Space n)}
    (w : ScalarLp p n Ω × VectorLp p n Ω) :
    w ∈ w0LpGraph p hp n Ω ↔
      ZeroBoundarySobolevPair p Ω (w.1 : Space n → ℝ) (w.2 : Space n → Space n) := Iff.rfl

theorem isClosed_w0LpGraph (hp : 1<p) (n : ℕ) (Ω : Set (Space n)) :
    IsClosed (w0LpGraph p hp n Ω : Set (ScalarLp p n Ω × VectorLp p n Ω)) := by
  apply IsSeqClosed.isClosed
  intro w z hw hz
  have h1 : Tendsto (fun j : ℕ => (w j).1) atTop (𝓝 z.1) := (continuous_fst.tendsto z).comp hz
  have h2 : Tendsto (fun j : ℕ => (w j).2) atTop (𝓝 z.2) := (continuous_snd.tendsto z).comp hz
  have huLim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (w j).1) z.1).mp h1
  have hgLim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (w j).2) z.2).mp h2
  exact zeroBoundarySobolevPair_of_eLpNorm_limits hp
    hw (by simpa using Lp.memLp z.1) (by simpa using Lp.memLp z.2)
    (by simpa using huLim) (by
      convert hgLim using 1
      funext j
      have hfg : (fun x => (w j).2 x-z.2 x) =
          ((w j).2 : Space n → Space n)-(z.2 : Space n → Space n) := rfl
      rw [hfg])

def w0LpGradient (hp : 1<p) (n : ℕ) (Ω : Set (Space n)) : w0LpGraph p hp n Ω →L[ℝ] VectorLp p n Ω :=
  (ContinuousLinearMap.snd ℝ (ScalarLp p n Ω) (VectorLp p n Ω)).comp (w0LpGraph p hp n Ω).subtypeL

theorem w0LpGradient_apply (hp : 1<p) {n : ℕ} {Ω : Set (Space n)} (w : w0LpGraph p hp n Ω) :
    w0LpGradient p hp n Ω w = w.1.2 := rfl

/-- The actual scalar W0 function is controlled by its actual weak gradient
in Lp, from the proved bounded-domain Poincare theorem. -/
theorem exists_w0Lp_scalar_norm_bound (hp : 1<p) {n : ℕ} (hpn : p<(n:ℝ))
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    ∃ C : ℝ≥0, ∀ w : w0LpGraph p hp n Ω, ‖w.1.1‖ ≤ C * ‖w.1.2‖ := by
  obtain ⟨C,hC⟩ := exists_W0_Lp_poincare_constant (p := p) hp hpn hΩb
  refine ⟨C,?_⟩
  intro w
  have he := hC w.2
  have he' : eLpNorm (w.1.1 : Space n → ℝ) (ENNReal.ofReal p) (volume.restrict Ω) ≤
      C * eLpNorm (w.1.2 : Space n → Space n) (ENNReal.ofReal p) (volume.restrict Ω) := by simpa using he
  have hf : (C : ℝ≥0∞) * eLpNorm (w.1.2 : Space n → Space n) (ENNReal.ofReal p) (volume.restrict Ω) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top w.1.2)
  have hreal := ENNReal.toReal_mono hf he'
  simpa only [Lp.norm_def,ENNReal.toReal_mul,ENNReal.coe_toReal] using hreal

theorem exists_w0LpGradient_antilipschitz (hp : 1<p) {n : ℕ} (hpn : p<(n:ℝ))
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    ∃ K : ℝ≥0, AntilipschitzWith K (w0LpGradient p hp n Ω) := by
  obtain ⟨C,hC⟩ := exists_w0Lp_scalar_norm_bound p hp hpn hΩb
  let K : ℝ≥0 := max C 1
  have hCK : (C : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_max_left C 1)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_max_right C 1)
  refine ⟨K,(w0LpGradient p hp n Ω).antilipschitz_of_bound ?_⟩
  intro w
  change max ‖w.1.1‖ ‖w.1.2‖ ≤ (K : ℝ) * ‖w.1.2‖
  exact max_le ((hC w).trans (mul_le_mul_of_nonneg_right hCK (norm_nonneg _)))
    (le_mul_of_one_le_left (norm_nonneg _) hK1)

def w0LpGradientRange (hp : 1<p) (n : ℕ) (Ω : Set (Space n)) : Submodule ℝ (VectorLp p n Ω) :=
  (w0LpGradient p hp n Ω).toLinearMap.range

theorem isClosed_w0LpGradientRange (hp : 1<p) {n : ℕ} (hpn : p<(n:ℝ))
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    IsClosed (w0LpGradientRange p hp n Ω : Set (VectorLp p n Ω)) := by
  letI : CompleteSpace (w0LpGraph p hp n Ω) := (isClosed_w0LpGraph p hp n Ω).completeSpace_coe
  obtain ⟨K,hK⟩ := exists_w0LpGradient_antilipschitz p hp hpn hΩb
  exact hK.isClosed_range (w0LpGradient p hp n Ω).uniformContinuous

end BMCompactPDE
#print axioms BMCompactPDE.w0LpGraph_mem_iff
#print axioms BMCompactPDE.isClosed_w0LpGraph
#print axioms BMCompactPDE.w0LpGradient_apply
#print axioms BMCompactPDE.exists_w0Lp_scalar_norm_bound
#print axioms BMCompactPDE.exists_w0LpGradient_antilipschitz
#print axioms BMCompactPDE.isClosed_w0LpGradientRange
