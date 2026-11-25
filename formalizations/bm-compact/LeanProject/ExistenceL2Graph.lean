import RootW0Linear
import RootPoincare
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Sequences

/-! The actual W0 distributional graph as a closed submodule of the two L2
components. Its gradient range is genuinely closed by the proved bounded-domain
Poincare estimate, rather than assumed to be a closed vector space. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped ENNReal NNReal Topology ContDiff
namespace BMCompactPDE

abbrev ScalarL2 (n : ℕ) (Ω : Set (Space n)) := Lp ℝ 2 (volume.restrict Ω)
abbrev VectorL2 (n : ℕ) (Ω : Set (Space n)) := Lp (Space n) 2 (volume.restrict Ω)

def w0L2Graph (n : ℕ) (Ω : Set (Space n)) :
    Submodule ℝ (ScalarL2 n Ω × VectorL2 n Ω) where
  carrier := {w | ZeroBoundarySobolevPair 2 Ω (w.1 : Space n → ℝ) (w.2 : Space n → Space n)}
  zero_mem' := by
    exact (zeroBoundarySobolevPair_zero (n := n) (p := 2) (by norm_num) Ω).congr
      (Lp.coeFn_zero ℝ 2 (volume.restrict Ω)).symm
      (Lp.coeFn_zero (Space n) 2 (volume.restrict Ω)).symm
  add_mem' := by
    intro x y hx hy
    exact (ZeroBoundarySobolevPair.add_actual hx hy).congr (Lp.coeFn_add x.1 y.1).symm (Lp.coeFn_add x.2 y.2).symm
  smul_mem' := by
    intro c x hx
    exact (ZeroBoundarySobolevPair.smul_actual hx c).congr (Lp.coeFn_smul c x.1).symm (Lp.coeFn_smul c x.2).symm

theorem w0L2Graph_mem_iff {n : ℕ} {Ω : Set (Space n)}
    (w : ScalarL2 n Ω × VectorL2 n Ω) :
    w ∈ w0L2Graph n Ω ↔
      ZeroBoundarySobolevPair 2 Ω (w.1 : Space n → ℝ) (w.2 : Space n → Space n) := Iff.rfl

theorem isClosed_w0L2Graph (n : ℕ) (Ω : Set (Space n)) :
    IsClosed (w0L2Graph n Ω : Set (ScalarL2 n Ω × VectorL2 n Ω)) := by
  apply IsSeqClosed.isClosed
  intro w z hw hz
  have h1 : Tendsto (fun j : ℕ => (w j).1) atTop (𝓝 z.1) := (continuous_fst.tendsto z).comp hz
  have h2 : Tendsto (fun j : ℕ => (w j).2) atTop (𝓝 z.2) := (continuous_snd.tendsto z).comp hz
  have huLim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (w j).1) z.1).mp h1
  have hgLim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (w j).2) z.2).mp h2
  exact zeroBoundarySobolevPair_of_eLpNorm_limits (by norm_num)
    hw (by simpa using Lp.memLp z.1) (by simpa using Lp.memLp z.2)
    (by simpa using huLim) (by
      convert hgLim using 1
      funext j
      have hfg : (fun x => (w j).2 x-z.2 x) =
          ((w j).2 : Space n → Space n)-(z.2 : Space n → Space n) := rfl
      rw [hfg,ENNReal.ofReal_ofNat])

def w0L2Gradient (n : ℕ) (Ω : Set (Space n)) : w0L2Graph n Ω →L[ℝ] VectorL2 n Ω :=
  (ContinuousLinearMap.snd ℝ (ScalarL2 n Ω) (VectorL2 n Ω)).comp (w0L2Graph n Ω).subtypeL

theorem w0L2Gradient_apply {n : ℕ} {Ω : Set (Space n)} (w : w0L2Graph n Ω) :
    w0L2Gradient n Ω w = w.1.2 := rfl

/-- The actual scalar W0 function is controlled by its actual weak gradient
in L2, from the proved bounded-domain Poincare theorem. -/
theorem exists_w0L2_scalar_norm_bound {n : ℕ} (hn : 3 ≤ n)
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    ∃ C : ℝ≥0, ∀ w : w0L2Graph n Ω, ‖w.1.1‖ ≤ C * ‖w.1.2‖ := by
  have hpn : (2 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 2<3) hn)
  obtain ⟨C,hC⟩ := exists_W0_Lp_poincare_constant (p := 2) (by norm_num) hpn hΩb
  refine ⟨C,?_⟩
  intro w
  have he := hC w.2
  have he' : eLpNorm (w.1.1 : Space n → ℝ) 2 (volume.restrict Ω) ≤
      C * eLpNorm (w.1.2 : Space n → Space n) 2 (volume.restrict Ω) := by simpa using he
  have hf : (C : ℝ≥0∞) * eLpNorm (w.1.2 : Space n → Space n) 2 (volume.restrict Ω) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top w.1.2)
  have hreal := ENNReal.toReal_mono hf he'
  simpa only [Lp.norm_def,ENNReal.toReal_mul,ENNReal.coe_toReal] using hreal

theorem exists_w0L2Gradient_antilipschitz {n : ℕ} (hn : 3 ≤ n)
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    ∃ K : ℝ≥0, AntilipschitzWith K (w0L2Gradient n Ω) := by
  obtain ⟨C,hC⟩ := exists_w0L2_scalar_norm_bound hn hΩb
  let K : ℝ≥0 := max C 1
  have hCK : (C : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_max_left C 1)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (le_max_right C 1)
  refine ⟨K,(w0L2Gradient n Ω).antilipschitz_of_bound ?_⟩
  intro w
  change max ‖w.1.1‖ ‖w.1.2‖ ≤ (K : ℝ) * ‖w.1.2‖
  exact max_le ((hC w).trans (mul_le_mul_of_nonneg_right hCK (norm_nonneg _)))
    (le_mul_of_one_le_left (norm_nonneg _) hK1)

def w0L2GradientRange (n : ℕ) (Ω : Set (Space n)) : Submodule ℝ (VectorL2 n Ω) :=
  (w0L2Gradient n Ω).toLinearMap.range

theorem isClosed_w0L2GradientRange {n : ℕ} (hn : 3 ≤ n)
    {Ω : Set (Space n)} (hΩb : Bornology.IsBounded Ω) :
    IsClosed (w0L2GradientRange n Ω : Set (VectorL2 n Ω)) := by
  letI : CompleteSpace (w0L2Graph n Ω) := (isClosed_w0L2Graph n Ω).completeSpace_coe
  obtain ⟨K,hK⟩ := exists_w0L2Gradient_antilipschitz hn hΩb
  exact hK.isClosed_range (w0L2Gradient n Ω).uniformContinuous

end BMCompactPDE
#print axioms BMCompactPDE.w0L2Graph_mem_iff
#print axioms BMCompactPDE.isClosed_w0L2Graph
#print axioms BMCompactPDE.w0L2Gradient_apply
#print axioms BMCompactPDE.exists_w0L2_scalar_norm_bound
#print axioms BMCompactPDE.exists_w0L2Gradient_antilipschitz
#print axioms BMCompactPDE.isClosed_w0L2GradientRange
