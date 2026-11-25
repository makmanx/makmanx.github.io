import RootCompactSobolevDensity
import RegCaccioppoliCutoff

/-! Ordinary smooth integer cutoffs are genuine full-W0 tests for arbitrary
weak solutions. The energy estimate has no test-admissibility, continuity or
classical differentiability premise on the weak representative. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem WeakPHarmonicPair.caccioppoli_natPow
    {n M : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η)
    (hη0 : ∀ x, 0 ≤ η x) (hη1 : ∀ x, η x ≤ 1)
    (hm : p ≤ (M : ℝ)) (k : ℝ) :
    (∫ x in D, η x^M*‖g x‖^p) ≤
      (M : ℝ)^p * ∫ x in D, |u x-k|^p * ‖gradient η x‖^p := by
  have hM : M ≠ 0 := by
    intro h
    have hp : p≤0 := by simpa only [h,Nat.cast_zero] using hm
    linarith [hu.1]
  have hM1 : 1≤M := Nat.one_le_iff_ne_zero.mpr hM
  have hcast : ((M-1 : ℕ) : ℝ) = (M : ℝ)-1 := by
    rw [Nat.cast_sub hM1]
    norm_num
  have hpow := hη.natPow_cutoff hM
  have ht := ((hu.sub_const k).2.2.1 D hD).mul_smooth_compactSupport_zeroBoundary
    hD.1 hpow.1 hpow.2.1 hpow.2.2
  have hηd := hη.1.differentiable (by simp)
  have heU : (fun x => η x^M*(u x-k)) =
      (fun x => η x^(M : ℝ)*(u x-k)) := by
    funext x
    rw [Real.rpow_natCast]
  have heG : (fun x => η x^M • g x+(u x-k) • gradient (fun y => η y^M) x) =
      (fun x => η x^(M : ℝ) • g x+
        ((M : ℝ)*η x^((M : ℝ)-1)*(u x-k)) • gradient η x) := by
    funext x
    rw [Real.rpow_natCast,←hcast,Real.rpow_natCast,gradient_natPow_cutoff hηd]
    simp only [smul_smul]
    congr 2
    ring
  rw [heU,heG] at ht
  have he := hu.caccioppoli_of_cutoff_W0 hD hη hη0 hη1 hm k ht
  simpa only [Real.rpow_natCast] using he

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.caccioppoli_natPow
