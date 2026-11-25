import RootSobolevMultiplier
import RegCaccioppoliCutoff

/-! Concrete weak cutoff-product graph and support control. The weak solution
has no classical differentiability hypothesis. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
namespace BMCompactPDE

theorem WeakPHarmonicPair.cutoff_natPow_sobolev_and_support
    {n M : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hD : LocalDomain D Ω)
    {η : Space n → ℝ} (hη : SmoothTest D η) (hM : M ≠ 0) (k : ℝ) :
    SobolevPair p D (fun x => η x^M*(u x-k))
      (fun x => η x^M • g x +
        ((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x) ∧
    tsupport (fun x => η x^M*(u x-k)) ⊆ tsupport η ∧
    tsupport (fun x => η x^M • g x +
      ((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x) ⊆ tsupport η := by
  have hz : (0 : ℝ)^M=0 := zero_pow hM
  have hpow := hη.natPow_cutoff hM
  have hs := ((hu.sub_const k).2.2.1 D hD).mul_smooth_compactSupport hpow.1 hpow.2.1
  have hηd := hη.1.differentiable (by simp)
  have he : (fun x => η x^M • g x+(u x-k) • gradient (fun y => η y^M) x) =
      (fun x => η x^M • g x+((M : ℝ)*η x^(M-1)*(u x-k)) • gradient η x) := by
    funext x
    rw [gradient_natPow_cutoff hηd]
    simp only [smul_smul]
    congr 2
    ring
  rw [he] at hs
  refine ⟨hs,?_,?_⟩
  · have hsu : tsupport (fun x => η x^M*(u x-k)) ⊆ tsupport (fun x => η x^M) :=
      tsupport_mul_subset_left
    exact hsu.trans (tsupport_comp_subset (g := fun z : ℝ => z^M) hz η)
  · apply closure_minimal ?_ (isClosed_tsupport η)
    intro x hx
    by_contra hn
    have hηx : η x=0 := image_eq_zero_of_notMem_tsupport hn
    have hgrad : gradient η x=0 := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport hn
    simp only [Function.mem_support] at hx
    simp only [hηx,hz,zero_smul,hgrad,smul_zero,add_zero,ne_eq,not_true_eq_false] at hx

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.cutoff_natPow_sobolev_and_support
