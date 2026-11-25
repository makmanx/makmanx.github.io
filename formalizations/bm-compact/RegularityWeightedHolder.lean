import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Weighted level gates for an unbounded-input De Giorgi iteration. These
are actual Holder estimates for the indicated functions, not assumed sequence
recurrences. In the PDE application the smooth cutoff powers equal one on the
compact set where boundedness is to be concluded. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
namespace BMCompactPDE

/-- A gate bounded by one gains the larger exponent from a weighted lower
level, with no upper bound on the weak function. -/
theorem regularity_gate_lp_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {b z : α → ℝ} {p N c : ℝ}
    (hp : 0<p) (hpN : p<N) (hc : 0≤c)
    (hb0 : ∀ x, 0≤b x) (hb1 : ∀ x, b x≤1)
    (hz0 : ∀ x, 0≤z x) (hbz : ∀ x, b x≤c*z x) :
    eLpNorm' b N μ ≤
      (ENNReal.ofReal c*eLpNorm' z p μ) ^ (p/N) := by
  have hN : 0<N := hp.trans hpN
  have ha : 0<p/N := div_pos hp hN
  have ha1 : p/N≤1 := (div_le_one hN).mpr hpN.le
  have hm : eLpNorm' b N μ ≤
      eLpNorm' (fun x => ‖c*z x‖ ^ (p/N)) N μ := by
    apply eLpNorm'_mono_ae hN.le
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hb0 x),Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hc (hz0 x))]
      exact (Real.self_le_rpow_of_le_one (hb0 x) (hb1 x) ha1).trans
        (Real.rpow_le_rpow (hb0 x) (hbz x) ha.le))
  have he : N*(p/N)=p := by field_simp
  rw [eLpNorm'_norm_rpow _ _ _ ha,he] at hm
  have hs : (fun x => c*z x)=c • z := rfl
  rw [hs,eLpNorm'_const_smul c hp,Real.enorm_eq_ofReal hc] at hm
  exact hm

/-- Actual weighted Holder step between two truncation levels. The additional
weight supplies a gate whose high-exponent norm is controlled by the previous
weighted Lp tail; no a priori essential or pointwise bound on u is supplied. -/
theorem regularity_weighted_holder {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {u η : α → ℝ} {p q N k h : ℝ} (m s : ℕ)
    (hp : 0<p) (hpq : p<q) (hpN : p<N)
    (hrel : 1/p=1/q+1/N) (hkh : k<h)
    (hu : AEStronglyMeasurable u μ) (hη : AEStronglyMeasurable η μ)
    (hη0 : ∀ x, 0≤η x) (hη1 : ∀ x, η x≤1) :
    eLpNorm' (fun x => η x^(m+s)*max (u x-h) 0) p μ ≤
      eLpNorm' (fun x => η x^m*max (u x-k) 0) q μ *
        (ENNReal.ofReal ((h-k)⁻¹)*
          eLpNorm' (fun x => η x^s*max (u x-k) 0) p μ) ^ (p/N) := by
  let A : α → ℝ := fun x => η x^m*max (u x-k) 0
  let B : α → ℝ := fun x => if h<u x then η x^s else 0
  let Z : α → ℝ := fun x => η x^s*max (u x-k) 0
  have hδ : 0<h-k := sub_pos.mpr hkh
  have hmax : AEStronglyMeasurable (fun x => max (u x-k) 0) μ :=
    ((continuous_id.sub continuous_const).max continuous_const).comp_aestronglyMeasurable hu
  have hA : AEStronglyMeasurable A μ := (hη.pow m).mul hmax
  have hset : NullMeasurableSet {x | h<u x} μ :=
    nullMeasurableSet_lt aemeasurable_const hu.aemeasurable
  have hB : AEStronglyMeasurable B μ := (hη.pow s).indicator₀ hset
  have hB0 (x : α) : 0≤B x := by
    dsimp only [B];split_ifs
    · exact pow_nonneg (hη0 x) s
    · exact le_rfl
  have hB1 (x : α) : B x≤1 := by
    dsimp only [B];split_ifs
    · exact pow_le_one₀ (hη0 x) (hη1 x)
    · norm_num
  have hZ0 (x : α) : 0≤Z x :=
    mul_nonneg (pow_nonneg (hη0 x) s) (le_max_right _ _)
  have hBZ (x : α) : B x≤(h-k)⁻¹*Z x := by
    dsimp only [B,Z]
    by_cases hx : h<u x
    · rw [if_pos hx,max_eq_left (by linarith : 0≤u x-k)]
      have hd : 1≤(h-k)⁻¹*(u x-k) := by
        rw [←div_eq_inv_mul]
        exact (one_le_div hδ).mpr (by linarith)
      calc
        η x^s = η x^s*1 := (mul_one _).symm
        _ ≤ η x^s*((h-k)⁻¹*(u x-k)) :=
          mul_le_mul_of_nonneg_left hd (pow_nonneg (hη0 x) s)
        _ = (h-k)⁻¹*(η x^s*(u x-k)) := by ring
    · rw [if_neg hx]
      exact mul_nonneg (inv_nonneg.mpr hδ.le) (hZ0 x)
  have hgate := regularity_gate_lp_bound (μ := μ) hp hpN (inv_nonneg.mpr hδ.le)
    hB0 hB1 hZ0 hBZ
  have hmono : eLpNorm' (fun x => η x^(m+s)*max (u x-h) 0) p μ ≤
      eLpNorm' (A*B) p μ := by
    apply eLpNorm'_mono_ae hp.le
    exact Eventually.of_forall (fun x => by
      have hpow : 0≤η x^(m+s) := pow_nonneg (hη0 x) _
      have hleft : 0≤η x^(m+s)*max (u x-h) 0 :=
        mul_nonneg hpow (le_max_right _ _)
      have hright : 0≤(A*B) x := mul_nonneg
        (mul_nonneg (pow_nonneg (hη0 x) _) (le_max_right _ _)) (hB0 x)
      rw [Real.norm_eq_abs,abs_of_nonneg hleft,Real.norm_eq_abs,abs_of_nonneg hright]
      dsimp only [A,B,Pi.mul_apply]
      by_cases hx : h<u x
      · rw [if_pos hx,pow_add]
        have hw : max (u x-h) 0≤max (u x-k) 0 := max_le_max (by linarith) le_rfl
        calc
          (η x^m*η x^s)*max (u x-h) 0 ≤
              (η x^m*η x^s)*max (u x-k) 0 :=
            mul_le_mul_of_nonneg_left hw
              (mul_nonneg (pow_nonneg (hη0 x) m) (pow_nonneg (hη0 x) s))
          _ = η x^m*max (u x-k) 0*η x^s := by ring
      · rw [if_neg hx,max_eq_right (by linarith : u x-h≤0)]
        simp)
  have hh := eLpNorm'_smul_le_mul_eLpNorm' (f := B) hB (φ := A) hA hp hpq hrel
  change eLpNorm' (A*B) p μ≤eLpNorm' A q μ*eLpNorm' B N μ at hh
  exact hmono.trans (hh.trans (mul_le_mul_of_nonneg_left hgate bot_le))

end BMCompactPDE
#print axioms BMCompactPDE.regularity_gate_lp_bound
#print axioms BMCompactPDE.regularity_weighted_holder
