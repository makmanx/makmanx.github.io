import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.Rademacher

/-! Null-set preservation for Lipschitz maps and zero-Jacobian sets on
finite-dimensional real normed spaces with AddHaar measure. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal
namespace BMCompactPDE

theorem addHaar_image_eq_zero_of_lipschitzOnWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : ℝ≥0} {f : E → E} {s : Set E}
    (hf : LipschitzOnWith K f s) (hs : μ s = 0) :
    μ (f '' s) = 0 := by
  classical
  let L : ℝ≥0 := max K 1
  have hL : LipschitzOnWith L f s := hf.weaken (le_max_left K 1)
  have hLpos : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast le_max_right K 1)
  let d : ℕ := Module.finrank ℝ E
  let C : ℝ≥0∞ := ENNReal.ofReal (4 * (L : ℝ)) ^ d
  have hC_ne_top : C ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine le_antisymm ?_ bot_le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [zero_add]
  have hC1 : C + 1 ≠ 0 := by positivity
  have hC1_top : C + 1 ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hC_ne_top, ENNReal.one_ne_top⟩
  let δ : ℝ≥0∞ := (ε : ℝ≥0∞) / (C + 1)
  have hδpos : 0 < δ := ENNReal.div_pos (ENNReal.coe_pos.mpr hε).ne' hC1_top
  have hlt : μ s < δ := by rw [hs]; exact hδpos
  obtain ⟨U, hsU, hUopen, hUlt⟩ := exists_isOpen_lt_of_lt s δ hlt
  have hex (x : E) (hx : x ∈ s) : ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ball x r ⊆ U := by
    obtain ⟨r0, hr0, hrU⟩ := Metric.isOpen_iff.mp hUopen x (hsU hx)
    refine ⟨min r0 1, lt_min hr0 zero_lt_one, min_le_right _ _, ?_⟩
    exact (ball_subset_ball (min_le_left _ _)).trans hrU
  let r : E → ℝ := fun x => if hx : x ∈ s then (hex x hx).choose else 0
  have hr_pos : ∀ x ∈ s, 0 < r x := fun x hx => by simp only [r, dif_pos hx]; exact (hex x hx).choose_spec.1
  have hr_le : ∀ x ∈ s, r x ≤ 1 := fun x hx => by simp only [r, dif_pos hx]; exact (hex x hx).choose_spec.2.1
  have hr_sub : ∀ x ∈ s, ball x (r x) ⊆ U := fun x hx => by simp only [r, dif_pos hx]; exact (hex x hx).choose_spec.2.2
  obtain ⟨u, hus, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball s id r 1 hr_le 4 (by norm_num)
  have hu_count : u.Countable := by
    apply hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    intro x hx
    exact ⟨x, mem_ball_self (hr_pos x (hus hx))⟩
  have hcov_img : f '' s ⊆ ⋃ b ∈ u, ball (f b) (4 * (L : ℝ) * r b) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, hbu, hbx⟩ := hcov x hx
    refine mem_iUnion₂.mpr ⟨b, hbu, ?_⟩
    have hxball : x ∈ ball b (4 * r b) := hbx (mem_ball_self (hr_pos x hx))
    rw [mem_ball] at hxball ⊢
    have hdist := hL.dist_le_mul x hx b (hus hbu)
    calc dist (f x) (f b) ≤ (L : ℝ) * dist x b := hdist
      _ < (L : ℝ) * (4 * r b) := mul_lt_mul_of_pos_left hxball hLpos
      _ = 4 * (L : ℝ) * r b := by ring
  have hball_eq (b : E) (hb : b ∈ u) :
      μ (ball (f b) (4 * (L : ℝ) * r b)) = C * μ (ball b (r b)) := by
    have hrb := hr_pos b (hus hb)
    have h4L : 0 < 4 * (L : ℝ) := by positivity
    rw [μ.addHaar_ball (f b) (mul_pos h4L hrb).le, μ.addHaar_ball b hrb.le,
      mul_pow, ENNReal.ofReal_mul (pow_nonneg h4L.le _), ENNReal.ofReal_pow h4L.le, mul_assoc]
  have : Countable u := hu_count.to_subtype
  have hsum_le : (∑' b : u, μ (ball (b : E) (r b))) ≤ μ U := by
    have hdisj' : Pairwise (Function.onFun Disjoint (fun b : u => ball (b : E) (r b))) :=
      fun a b hab => hdisj a.2 b.2 (Subtype.coe_ne_coe.mpr hab)
    rw [← measure_iUnion hdisj' (fun _ => isOpen_ball.measurableSet)]
    exact measure_mono (iUnion_subset fun b => hr_sub b.1 (hus b.2))
  calc μ (f '' s)
      ≤ μ (⋃ b ∈ u, ball (f b) (4 * (L : ℝ) * r b)) := measure_mono hcov_img
    _ ≤ ∑' b : u, μ (ball (f b) (4 * (L : ℝ) * r b)) := by
        rw [biUnion_eq_iUnion]; exact measure_iUnion_le _
    _ = ∑' b : u, C * μ (ball (b : E) (r b)) := by
        congr 1; ext b; exact hball_eq b.1 b.2
    _ = C * ∑' b : u, μ (ball (b : E) (r b)) := ENNReal.tsum_mul_left
    _ ≤ C * μ U := by gcongr
    _ ≤ C * δ := by gcongr
    _ ≤ (C + 1) * δ := by gcongr; exact le_self_add
    _ = (ε : ℝ≥0∞) := ENNReal.mul_div_cancel hC1 hC1_top

theorem addHaar_image_eq_zero_of_lipschitzWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : ℝ≥0} {f : E → E} {s : Set E}
    (hf : LipschitzWith K f) (hs : μ s = 0) :
    μ (f '' s) = 0 :=
  addHaar_image_eq_zero_of_lipschitzOnWith μ hf.lipschitzOnWith hs

end BMCompactPDE
#print axioms BMCompactPDE.addHaar_image_eq_zero_of_lipschitzOnWith
#print axioms BMCompactPDE.addHaar_image_eq_zero_of_lipschitzWith
