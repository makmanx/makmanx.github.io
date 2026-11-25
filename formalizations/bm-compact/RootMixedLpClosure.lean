import RootW0Linear
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Actual local graph closure from mixed global Lq scalar/Lp gradient limits.
The limiting scalar is not assumed globally Lp. Finite-volume restriction
proves its local Lp data and strong convergence. This supplies the genuine
function-valued homogeneous Sobolev graph needed for exterior construction. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace BMCompactPDE

theorem tendsto_eLpNorm_restrict_lower_exponent {n : ℕ} {p q : ℝ}
    (hp : 0<p) (hpq : p≤q) {D : Set (Space n)} (hDb : Bornology.IsBounded D)
    {F : Type*} [NormedAddCommGroup F] (f : ℕ → Space n → F)
    (hfm : ∀ j, AEStronglyMeasurable (f j) (volume.restrict D))
    (hlim : Tendsto (fun j => eLpNorm (f j) (ENNReal.ofReal q) volume) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (f j) (ENNReal.ofReal p) (volume.restrict D))
      atTop (𝓝 0) := by
  have hq : 0<q := hp.trans_le hpq
  let μ := volume.restrict D
  let C : ℝ≥0∞ := μ univ^(1/p-1/q)
  have hr : 0≤1/p-1/q := sub_nonneg.mpr (one_div_le_one_div_of_le hp hpq)
  have hDfinite : volume D≠(∞:ℝ≥0∞) := hDb.measure_lt_top.ne
  have hC : C≠(∞:ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg hr (by simpa only [μ,Measure.restrict_apply_univ] using hDfinite)
  have hb (j : ℕ) : eLpNorm (f j) (ENNReal.ofReal p) μ ≤
      eLpNorm (f j) (ENNReal.ofReal q) volume*C := by
    have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (ENNReal.ofReal_le_ofReal hpq) (hfm j)
    have he' : eLpNorm (f j) (ENNReal.ofReal p) μ ≤
        eLpNorm (f j) (ENNReal.ofReal q) μ*C := by
      simpa only [ENNReal.toReal_ofReal hp.le,ENNReal.toReal_ofReal hq.le] using he
    exact he'.trans (mul_le_mul_left (eLpNorm_mono_measure (f j) Measure.restrict_le_self) C)
  have ht := ENNReal.Tendsto.mul_const hlim (Or.inr hC)
  rw [zero_mul] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) hb

theorem sobolevPair_of_global_mixed_limits {n : ℕ} {p q : ℝ}
    (hp : 1<p) (hpq : p≤q) {D : Set (Space n)} (hDb : Bornology.IsBounded D)
    {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hu : ∀ j, SobolevPair p D (u j) (g j))
    (hv : MemLp v (ENNReal.ofReal q) volume)
    (hh : MemLp h (ENNReal.ofReal p) volume)
    (hlimu : Tendsto (fun j => eLpNorm (u j-v) (ENNReal.ofReal q) volume) atTop (𝓝 0))
    (hlimg : Tendsto (fun j => eLpNorm (fun x => g j x-h x) (ENNReal.ofReal p) volume)
      atTop (𝓝 0)) : SobolevPair p D v h := by
  letI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hDb.measure_lt_top.ne
  have hvD : MemLp v (ENNReal.ofReal p) (volume.restrict D) :=
    (hv.mono_measure Measure.restrict_le_self).mono_exponent (ENNReal.ofReal_le_ofReal hpq)
  have hhD : MemLp h (ENNReal.ofReal p) (volume.restrict D) :=
    hh.mono_measure Measure.restrict_le_self
  have hsu := tendsto_eLpNorm_restrict_lower_exponent (zero_lt_one.trans hp) hpq hDb
    (fun j => u j-v) (fun j => ((hu j).2.1.sub hvD).1) hlimu
  have hsg := tendsto_eLpNorm_restrict_lower_exponent (zero_lt_one.trans hp) le_rfl hDb
    (fun j x => g j x-h x) (fun j => ((hu j).2.2.1.sub hhD).1) hlimg
  exact sobolevPair_of_eLpNorm_limits hp hu hvD hhD hsu hsg

theorem localSobolevPair_of_smooth_mixed_limits {n : ℕ} {p q : ℝ}
    (hp : 1<p) (hpq : p≤q)
    {φ : ℕ → Space n → ℝ} (hφ : ∀ j, SmoothTest univ (φ j))
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : MemLp v (ENNReal.ofReal q) volume)
    (hh : MemLp h (ENNReal.ofReal p) volume)
    (hlimu : Tendsto (fun j => eLpNorm (φ j-v) (ENNReal.ofReal q) volume) atTop (𝓝 0))
    (hlimg : Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-h x)
      (ENNReal.ofReal p) volume) atTop (𝓝 0))
    {D : Set (Space n)} (hDb : Bornology.IsBounded D) : SobolevPair p D v h := by
  exact sobolevPair_of_global_mixed_limits hp hpq hDb
    (fun j => ((hφ j).sobolevPair hp).mono_actual (subset_univ D)) hv hh hlimu hlimg

end BMCompactPDE
#print axioms BMCompactPDE.tendsto_eLpNorm_restrict_lower_exponent
#print axioms BMCompactPDE.sobolevPair_of_global_mixed_limits
#print axioms BMCompactPDE.localSobolevPair_of_smooth_mixed_limits
