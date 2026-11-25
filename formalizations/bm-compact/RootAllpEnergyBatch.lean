import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import NonlinearClarkson
import RootEnergyMin

/-! All-p bounded energy-gap foundations, counted once after checking. -/
section RootAllpSegment_RootPowerGap

/-! Actual pointwise power-energy separation for every p>1. Properness is
used only for a compact pair of value-space unit balls, not for the infinite-
dimensional Sobolev or Lp function space. -/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace BMCompactBanach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [StrictConvexSpace ℝ E]

theorem norm_rpow_midpoint_lt {p : ℝ} (hp : 1<p) {x y : E} (hxy : x≠y) :
    ‖(1/2 : ℝ) • (x+y)‖^p < (‖x‖^p+‖y‖^p)/2 := by
  have hp0 : 0<p := zero_lt_one.trans hp
  by_cases he : ‖x‖=‖y‖
  · have hm := (norm_midpoint_lt_iff he).mpr hxy
    have hh := Real.rpow_lt_rpow (norm_nonneg _) hm hp0
    rw [he] at hh
    rw [he]
    nlinarith only [hh]
  · have hm : ‖(1/2 : ℝ) • (x+y)‖ ≤ (1/2 : ℝ)*‖x‖+(1/2 : ℝ)*‖y‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      exact (mul_le_mul_of_nonneg_left (norm_add_le x y) (by norm_num)).trans_eq (by ring)
    have hh := Real.rpow_le_rpow (norm_nonneg _) hm hp0.le
    have hs := (strictConvexOn_rpow hp).2 (norm_nonneg x) (norm_nonneg y) he
      (by norm_num : (0 : ℝ)<1/2) (by norm_num : (0 : ℝ)<1/2)
      (by norm_num : (1/2 : ℝ)+1/2=1)
    simp only [smul_eq_mul] at hs
    nlinarith only [hh,hs]

def normPowerMidpointGap (p : ℝ) (x y : E) : ℝ :=
  (‖x‖^p+‖y‖^p)/2-‖(1/2 : ℝ) • (x+y)‖^p

theorem exists_unit_normPowerMidpointGap [ProperSpace E] {p τ : ℝ}
    (hp : 1<p) (hτ : 0<τ) :
    ∃ κ : ℝ,0<κ ∧ ∀ x y : E,‖x‖≤1 → ‖y‖≤1 → τ≤‖x-y‖ →
      κ≤normPowerMidpointGap p x y := by
  let S : Set (E×E) := (closedBall (0 : E) 1 ×ˢ closedBall (0 : E) 1) ∩
    {z | τ≤‖z.1-z.2‖}
  have hSc : IsCompact S :=
    ((isCompact_closedBall (0 : E) 1).prod (isCompact_closedBall (0 : E) 1)).inter_right
      (isClosed_le continuous_const ((continuous_fst.sub continuous_snd).norm))
  have hmem (x y : E) : (x,y)∈S ↔ ‖x‖≤1 ∧ ‖y‖≤1 ∧ τ≤‖x-y‖ := by
    simp only [S,mem_inter_iff,mem_prod,mem_closedBall_zero_iff,mem_setOf_eq,and_assoc]
  have hpow : Continuous (fun a : ℝ=>a^p) :=
    continuous_id.rpow_const (fun _=>Or.inr (zero_lt_one.trans hp).le)
  have hG : Continuous (fun z : E×E=>normPowerMidpointGap p z.1 z.2) := by
    dsimp only [normPowerMidpointGap]
    exact ((hpow.comp continuous_fst.norm).add (hpow.comp continuous_snd.norm)).div_const 2 |>.sub
      (hpow.comp (((continuous_fst.add continuous_snd).const_smul (1/2 : ℝ)).norm))
  by_cases hne : S.Nonempty
  · obtain ⟨z,hz,hmin⟩ := hSc.exists_isMinOn hne hG.continuousOn
    have hz' := (hmem z.1 z.2).mp hz
    have hxy : z.1≠z.2 := by
      intro he
      have hh : τ≤0 := by simpa [he] using hz'.2.2
      exact (not_le_of_gt hτ) hh
    have hpos : 0<normPowerMidpointGap p z.1 z.2 := by
      have hh := norm_rpow_midpoint_lt hp hxy
      dsimp only [normPowerMidpointGap]
      linarith
    refine ⟨_,hpos,?_⟩
    intro x y hx hy hsep
    exact hmin ((hmem x y).mpr ⟨hx,hy,hsep⟩)
  · refine ⟨1,zero_lt_one,?_⟩
    intro x y hx hy hsep
    exact (hne ⟨(x,y),(hmem x y).mpr ⟨hx,hy,hsep⟩⟩).elim

end BMCompactBanach
end -- original noncomputable section
end RootAllpSegment_RootPowerGap

section RootAllpSegment_RootRelativeGap

/-! Actual homogeneous relative energy separation for every p>1. -/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace BMCompactBanach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [StrictConvexSpace ℝ E]

theorem normPowerMidpointGap_nonneg {p : ℝ} (hp : 1<p) (x y : E) :
    0≤normPowerMidpointGap p x y := by
  by_cases h : x=y
  · subst y
    have hm : (1/2 : ℝ) • (x+x)=x := by module
    simp only [normPowerMidpointGap,hm]
    linarith
  · have hh := norm_rpow_midpoint_lt hp h
    dsimp only [normPowerMidpointGap]
    linarith

theorem normPowerMidpointGap_smul (p : ℝ) {r : ℝ} (hr : 0≤r) (x y : E) :
    normPowerMidpointGap p (r • x) (r • y)=r^p*normPowerMidpointGap p x y := by
  have hm : (1/2 : ℝ) • (r • x+r • y)=r • ((1/2 : ℝ) • (x+y)) := by module
  dsimp only [normPowerMidpointGap]
  rw [hm]
  simp only [norm_smul_of_nonneg hr]
  rw [Real.mul_rpow hr (norm_nonneg x),Real.mul_rpow hr (norm_nonneg y),
    Real.mul_rpow hr (norm_nonneg ((1/2 : ℝ) • (x+y)))]
  ring

theorem exists_relative_power_gap_control [ProperSpace E] {p τ : ℝ}
    (hp : 1<p) (hτ : 0<τ) :
    ∃ κ : ℝ,0<κ ∧ ∀ x y : E,
      ‖x-y‖^p ≤ (τ*(‖x‖+‖y‖))^p+normPowerMidpointGap p x y/κ := by
  have hp0 : 0<p := zero_lt_one.trans hp
  obtain ⟨κ,hκ,hmod⟩ := exists_unit_normPowerMidpointGap (E := E) hp hτ
  refine ⟨κ,hκ,?_⟩
  intro x y
  have hG := normPowerMidpointGap_nonneg hp x y
  by_cases hsep : τ*(‖x‖+‖y‖)≤‖x-y‖
  · let s : ℝ := ‖x‖+‖y‖
    have hs0 : 0≤s := add_nonneg (norm_nonneg _) (norm_nonneg _)
    by_cases hs : 0<s
    · let a := s⁻¹ • x
      let b := s⁻¹ • y
      have ha : ‖a‖≤1 := by
        dsimp only [a]
        rw [norm_smul_of_nonneg (inv_nonneg.mpr hs.le)]
        exact (mul_le_mul_of_nonneg_left (by dsimp only [s]; exact le_add_of_nonneg_right (norm_nonneg y) : ‖x‖≤s)
          (inv_nonneg.mpr hs.le)).trans_eq (inv_mul_cancel₀ hs.ne')
      have hb : ‖b‖≤1 := by
        dsimp only [b]
        rw [norm_smul_of_nonneg (inv_nonneg.mpr hs.le)]
        exact (mul_le_mul_of_nonneg_left (by dsimp only [s]; exact le_add_of_nonneg_left (norm_nonneg x) : ‖y‖≤s)
          (inv_nonneg.mpr hs.le)).trans_eq (inv_mul_cancel₀ hs.ne')
      have hdist : ‖a-b‖=s⁻¹*‖x-y‖ := by
        dsimp only [a,b]
        rw [←smul_sub,norm_smul_of_nonneg (inv_nonneg.mpr hs.le)]
      have hab : τ≤‖a-b‖ := by
        rw [hdist,←div_eq_inv_mul]
        exact (le_div_iff₀ hs).mpr hsep
      have hm := hmod a b ha hb hab
      have hx : s • a=x := by dsimp [a];simp [smul_smul,hs.ne']
      have hy : s • b=y := by dsimp [b];simp [smul_smul,hs.ne']
      have hscale : normPowerMidpointGap p x y=s^p*normPowerMidpointGap p a b := by
        simpa only [hx,hy] using normPowerMidpointGap_smul p hs.le a b
      have hdp : ‖x-y‖^p≤s^p :=
        Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le x y) hp0.le
      have hfar : ‖x-y‖^p≤normPowerMidpointGap p x y/κ := by
        apply (le_div_iff₀ hκ).mpr
        rw [hscale]
        exact (mul_le_mul_of_nonneg_right hdp hκ.le).trans
          (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hs0 p))
      exact hfar.trans (le_add_of_nonneg_left (Real.rpow_nonneg (mul_nonneg hτ.le hs0) p))
    · have hsZ : s=0 := le_antisymm (le_of_not_gt hs) hs0
      have hx : x=0 := norm_eq_zero.mp (by dsimp [s] at hsZ; have := norm_nonneg y; nlinarith [norm_nonneg x])
      have hy : y=0 := norm_eq_zero.mp (by dsimp [s] at hsZ; have := norm_nonneg x; nlinarith [norm_nonneg y])
      subst x;subst y
      simp [normPowerMidpointGap,Real.zero_rpow hp0.ne']
  · have hm := Real.rpow_le_rpow (norm_nonneg _) (le_of_not_ge hsep) hp0.le
    exact hm.trans (le_add_of_nonneg_right (div_nonneg hG hκ.le))

end BMCompactBanach
end -- original noncomputable section
end RootAllpSegment_RootRelativeGap

section RootAllpSegment_RootLpEnergyGap

/-! Genuine bounded-norm midpoint separation in Hilbert-valued Lp for ALL p>1.
Compactness is used in the proper finite-dimensional value space only. The
infinite-dimensional function space is not assumed compact or reflexive. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ENNReal NNReal
namespace BMCompactBanach
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    [StrictConvexSpace ℝ E]
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ}
    [Fact (1≤ENNReal.ofReal p)]

theorem lp_bounded_midpoint_gap (hp : 1<p) (R ε : ℝ) (hε : 0<ε) :
    ∃ κ : ℝ,0<κ ∧ ∀ f g : Lp E (ENNReal.ofReal p) μ,
      ‖f‖≤R → ‖g‖≤R → ε≤‖f-g‖ →
      κ≤(‖f‖^p+‖g‖^p)/2-‖(1/2 : ℝ) • (f+g)‖^p := by
  have hp0 : 0<p := zero_lt_one.trans hp
  by_cases hR : 0<R
  · let τ := ε/(4*R)
    have hτ : 0<τ := div_pos hε (by positivity)
    obtain ⟨δ,hδ,hrel⟩ := exists_relative_power_gap_control (E := E) hp hτ
    have hpow : (ε/2)^p<ε^p :=
      Real.rpow_lt_rpow (by positivity) (by linarith) hp0
    refine ⟨δ*(ε^p-(ε/2)^p),mul_pos hδ (sub_pos.mpr hpow),?_⟩
    intro f g hf hg hsep
    let q := ENNReal.ofReal p
    have hfN := (Lp.memLp f).norm
    have hgN := (Lp.memLp g).norm
    let F : Lp ℝ q μ := hfN.toLp (fun x=>‖f x‖)
    let G : Lp ℝ q μ := hgN.toLp (fun x=>‖g x‖)
    let N := F+G
    let H := (1/2 : ℝ) • (f+g)
    have hF : ‖F‖=‖f‖ := by
      dsimp only [F]
      rw [Lp.norm_toLp,Lp.norm_def,eLpNorm_norm]
    have hG : ‖G‖=‖g‖ := by
      dsimp only [G]
      rw [Lp.norm_toLp,Lp.norm_def,eLpNorm_norm]
    have hNbound : ‖N‖≤2*R := by
      have hh := norm_add_le F G
      rw [hF,hG] at hh
      dsimp only [N]
      linarith only [hh,hf,hg]
    have hNae : (fun x=>‖N x‖^p) =ᵐ[μ] (fun x=>(‖f x‖+‖g x‖)^p) := by
      filter_upwards [Lp.coeFn_add F G,MemLp.coeFn_toLp hfN,MemLp.coeFn_toLp hgN]
        with x hadd hFx hGx
      change ‖(F+G) x‖^p=(‖f x‖+‖g x‖)^p
      rw [hadd]
      change ‖F x+G x‖^p=_
      rw [hFx,hGx,Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    have hMI : Integrable (fun x=>(‖f x‖+‖g x‖)^p) μ :=
      (BMCompactNonlinear.lp_norm_rpow_integrable hp0 N).congr hNae
    have hMbound : (∫ x,(‖f x‖+‖g x‖)^p ∂μ)≤(2*R)^p := by
      have he : (∫ x,(‖f x‖+‖g x‖)^p ∂μ)=‖N‖^p :=
        (integral_congr_ae hNae).symm.trans (BMCompactNonlinear.lp_norm_rpow_eq_integral hp0 N).symm
      rw [he]
      exact Real.rpow_le_rpow (norm_nonneg _) hNbound hp0.le
    have hDae : (fun x=>‖(f-g) x‖^p) =ᵐ[μ] (fun x=>‖f x-g x‖^p) := by
      filter_upwards [Lp.coeFn_sub f g] with x hx
      rw [hx]
      rfl
    have hDI : Integrable (fun x=>‖f x-g x‖^p) μ :=
      (BMCompactNonlinear.lp_norm_rpow_integrable hp0 (f-g)).congr hDae
    have hDeq : (∫ x,‖f x-g x‖^p ∂μ)=‖f-g‖^p :=
      (integral_congr_ae hDae).symm.trans (BMCompactNonlinear.lp_norm_rpow_eq_integral hp0 (f-g)).symm
    have hHae : (fun x=>‖H x‖^p) =ᵐ[μ] (fun x=>‖(1/2 : ℝ) • (f x+g x)‖^p) := by
      filter_upwards [Lp.coeFn_smul (1/2 : ℝ) (f+g),Lp.coeFn_add f g] with x hsm hadd
      change ‖((1/2 : ℝ) • (f+g)) x‖^p=_
      rw [hsm]
      change ‖(1/2 : ℝ) • (f+g) x‖^p=_
      rw [hadd]
      rfl
    have hHI : Integrable (fun x=>‖(1/2 : ℝ) • (f x+g x)‖^p) μ :=
      (BMCompactNonlinear.lp_norm_rpow_integrable hp0 H).congr hHae
    have hHeq : (∫ x,‖(1/2 : ℝ) • (f x+g x)‖^p ∂μ)=‖H‖^p :=
      (integral_congr_ae hHae).symm.trans (BMCompactNonlinear.lp_norm_rpow_eq_integral hp0 H).symm
    have hfI := BMCompactNonlinear.lp_norm_rpow_integrable hp0 f
    have hgI := BMCompactNonlinear.lp_norm_rpow_integrable hp0 g
    have hGI : Integrable (fun x=>normPowerMidpointGap p (f x) (g x)) μ := by
      exact ((hfI.add hgI).div_const 2).sub hHI
    have hGeq : (∫ x,normPowerMidpointGap p (f x) (g x) ∂μ)=
        (‖f‖^p+‖g‖^p)/2-‖H‖^p := by
      change (∫ x,(‖f x‖^p+‖g x‖^p)/2-‖(1/2 : ℝ) • (f x+g x)‖^p ∂μ)=_
      have hsub : (∫ x,(‖f x‖^p+‖g x‖^p)/2-‖(1/2 : ℝ) • (f x+g x)‖^p ∂μ)=
          (∫ x,(‖f x‖^p+‖g x‖^p)/2 ∂μ)-(∫ x,‖(1/2 : ℝ) • (f x+g x)‖^p ∂μ) :=
        integral_sub ((hfI.add hgI).div_const 2) hHI
      have hadd : (∫ x,‖f x‖^p+‖g x‖^p ∂μ)=
          (∫ x,‖f x‖^p ∂μ)+(∫ x,‖g x‖^p ∂μ) := integral_add hfI hgI
      rw [hsub,integral_div,hadd,
        ←BMCompactNonlinear.lp_norm_rpow_eq_integral hp0 f,
        ←BMCompactNonlinear.lp_norm_rpow_eq_integral hp0 g,hHeq]
    have hpoint : (fun x=>‖f x-g x‖^p) ≤ᵐ[μ]
        (fun x=>τ^p*(‖f x‖+‖g x‖)^p+normPowerMidpointGap p (f x) (g x)/δ) := by
      exact Eventually.of_forall (fun x=>by
        simpa only [Real.mul_rpow hτ.le (add_nonneg (norm_nonneg _) (norm_nonneg _))] using hrel (f x) (g x))
    have hi := integral_mono_ae hDI ((hMI.const_mul (τ^p)).add (hGI.div_const δ)) hpoint
    change (∫ x,‖f x-g x‖^p ∂μ)≤
      (∫ x,τ^p*(‖f x‖+‖g x‖)^p+normPowerMidpointGap p (f x) (g x)/δ ∂μ) at hi
    have hsplit : (∫ x,τ^p*(‖f x‖+‖g x‖)^p+normPowerMidpointGap p (f x) (g x)/δ ∂μ)=
        (∫ x,τ^p*(‖f x‖+‖g x‖)^p ∂μ)+(∫ x,normPowerMidpointGap p (f x) (g x)/δ ∂μ) :=
      integral_add (hMI.const_mul (τ^p)) (hGI.div_const δ)
    rw [hsplit,integral_const_mul,integral_div,hDeq,hGeq] at hi
    have hscale : τ^p*(2*R)^p=(ε/2)^p := by
      rw [←Real.mul_rpow hτ.le (by positivity : (0 : ℝ)≤2*R)]
      congr 1
      dsimp only [τ]
      field_simp [hR.ne']
      ring
    have hsmall : τ^p*(∫ x,(‖f x‖+‖g x‖)^p ∂μ)≤(ε/2)^p :=
      (mul_le_mul_of_nonneg_left hMbound (Real.rpow_nonneg hτ.le p)).trans_eq hscale
    have hsepP := Real.rpow_le_rpow hε.le hsep hp0.le
    have hh : ε^p-(ε/2)^p≤((‖f‖^p+‖g‖^p)/2-‖H‖^p)/δ := by
      linarith only [hi,hsmall,hsepP]
    have he := (le_div_iff₀ hδ).mp hh
    simpa only [H,mul_comm] using he
  · refine ⟨1,zero_lt_one,?_⟩
    intro f g hf hg hsep
    have hh := norm_sub_le f g
    have hR0 : R≤0 := le_of_not_gt hR
    exact (not_le_of_gt hε (hsep.trans (by linarith only [hh,hf,hg,hR0]))).elim

end BMCompactBanach
end -- original noncomputable section
end RootAllpSegment_RootLpEnergyGap

section RootAllpSegment_RootBoundedEnergyMin

/-! Coercive direct minimization when the energy gap is uniform only on
bounded sets. This is the correct form for1<p<2; no global gap is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace BMCompactBanach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_minimum_of_coercive_bounded_midpoint_gap {K : Set E}
    (hne : K.Nonempty) (hclosed : IsClosed K) (hK : Convex ℝ K)
    {f : E → ℝ} (hf : ContinuousOn f K) (hbdd : BddBelow (f '' K))
    (hcoercive : ∀ a : ℝ,∃ R : ℝ,∀ x∈K,f x≤a → ‖x‖≤R)
    (hgap : ∀ R ε : ℝ,0<ε → ∃ κ : ℝ,0<κ ∧ ∀ x∈K,∀ y∈K,
      ‖x‖≤R → ‖y‖≤R → ε≤‖x-y‖ →
      f ((1/2 : ℝ) • x+(1/2 : ℝ) • y)≤(f x+f y)/2-κ) :
    ∃ v∈K,∀ z∈K,f v≤f z := by
  obtain ⟨x₀,hx₀⟩ := hne
  obtain ⟨R,hR⟩ := hcoercive (f x₀)
  let S := K ∩ closedBall (0 : E) R
  have hxS : x₀∈S := ⟨hx₀,mem_closedBall_zero_iff.mpr (hR x₀ hx₀ le_rfl)⟩
  have hSc : IsClosed S := hclosed.inter isClosed_closedBall
  have hSconv : Convex ℝ S := hK.inter (convex_closedBall (0 : E) R)
  have hfg : ∀ ε : ℝ,0<ε → ∃ κ : ℝ,0<κ ∧ ∀ x∈S,∀ y∈S,
      ε≤‖x-y‖ → f ((1/2 : ℝ) • x+(1/2 : ℝ) • y)≤(f x+f y)/2-κ := by
    intro ε hε
    obtain ⟨κ,hκ,hg⟩ := hgap R ε hε
    refine ⟨κ,hκ,?_⟩
    intro x hx y hy hsep
    exact hg x hx.1 y hy.1 (mem_closedBall_zero_iff.mp hx.2)
      (mem_closedBall_zero_iff.mp hy.2) hsep
  obtain ⟨v,hv,hm⟩ := exists_minimum_of_complete_midpoint_gap ⟨x₀,hxS⟩
    hSc.isComplete hSconv (hf.mono inter_subset_left)
    (hbdd.mono (image_mono inter_subset_left)) hfg
  refine ⟨v,hv.1,?_⟩
  intro z hz
  by_cases hzn : ‖z‖≤R
  · exact hm z ⟨hz,mem_closedBall_zero_iff.mpr hzn⟩
  · have hfx : f x₀<f z := lt_of_not_ge (fun h=>hzn (hR z hz h))
    exact (hm x₀ hxS).trans hfx.le

end BMCompactBanach
end -- original noncomputable section
end RootAllpSegment_RootBoundedEnergyMin

#print axioms BMCompactBanach.norm_rpow_midpoint_lt
#print axioms BMCompactBanach.exists_unit_normPowerMidpointGap
#print axioms BMCompactBanach.normPowerMidpointGap_nonneg
#print axioms BMCompactBanach.normPowerMidpointGap_smul
#print axioms BMCompactBanach.exists_relative_power_gap_control
#print axioms BMCompactBanach.lp_bounded_midpoint_gap
#print axioms BMCompactBanach.exists_minimum_of_coercive_bounded_midpoint_gap
