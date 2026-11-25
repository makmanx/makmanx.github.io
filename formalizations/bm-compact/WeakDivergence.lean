import LocalSmoothWeakBridge
import WeakDensity

/-!
Local classical divergence and the complete weak p-Laplace equation.
Smoothness is required only inside the open domain; no extension across a
singular point outside the domain is assumed.  Density supplies the passage
from compact smooth tests to every W^{1,p}_0 test.
-/

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology ContDiff InnerProductSpace

namespace BMCompactPDE

/-- Classical Euclidean divergence, as the sum of actual coordinate partials. -/
def coordinateDivergence {n : ℕ} (F : Space n → Space n) (x : Space n) : ℝ :=
  ∑ i : Fin n, (gradient (fun y => F y i) x) i

theorem integral_inner_gradient_eq_neg_divergence {n : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {F : Space n → Space n}
    (hF : ∀ i : Fin n, ContDiffOn ℝ ∞ (fun x => F x i) Ω)
    {φ : Space n → ℝ} (hφ : SmoothTest Ω φ) :
    Integrable (fun x => inner ℝ (F x) (gradient φ x)) (volume.restrict Ω) ∧
    Integrable (fun x => coordinateDivergence F x * φ x) (volume.restrict Ω) ∧
      (∫ x in Ω, inner ℝ (F x) (gradient φ x)) =
        -(∫ x in Ω, coordinateDivergence F x * φ x) := by
  let L : Fin n → Space n → ℝ := fun i x => F x i * (gradient φ x) i
  let R : Fin n → Space n → ℝ :=
    fun i x => (gradient (fun y => F y i) x) i * φ x
  have hcoord (i : Fin n) := hasWeakGradientOn_of_contDiffOn hΩ (hF i) φ hφ i
  have hLi (i : Fin n) : Integrable (L i) (volume.restrict Ω) := (hcoord i).1
  have hRi (i : Fin n) : Integrable (R i) (volume.restrict Ω) := (hcoord i).2.1
  have hL : Integrable (fun x => ∑ i : Fin n, L i x) (volume.restrict Ω) := by
    convert integrable_finsetSum Finset.univ (fun i _ => hLi i) using 1 <;> rfl
  have hR : Integrable (fun x => ∑ i : Fin n, R i x) (volume.restrict Ω) := by
    convert integrable_finsetSum Finset.univ (fun i _ => hRi i) using 1 <;> rfl
  have hinner : (fun x => inner ℝ (F x) (gradient φ x)) =
      (fun x => ∑ i : Fin n, L i x) := by
    funext x
    simp only [L, PiLp.inner_apply, Real.inner_apply]
  have hdiv : (fun x => coordinateDivergence F x * φ x) =
      (fun x => ∑ i : Fin n, R i x) := by
    funext x
    simp only [coordinateDivergence, Finset.sum_mul, R]
  refine ⟨?_, ?_, ?_⟩
  · rw [hinner]
    exact hL
  · rw [hdiv]
    exact hR
  · rw [hinner, hdiv, integral_finsetSum Finset.univ (fun i _ => hLi i),
      integral_finsetSum Finset.univ (fun i _ => hRi i)]
    calc
      (∑ i : Fin n, ∫ x in Ω, L i x) = ∑ i : Fin n, -(∫ x in Ω, R i x) :=
        Finset.sum_congr rfl (fun i _ => (hcoord i).2.2)
      _ = -(∑ i : Fin n, ∫ x in Ω, R i x) :=
        Finset.sum_neg_distrib (fun i : Fin n => ∫ x in Ω, R i x)

theorem integral_inner_gradient_eq_zero_of_divergence_eq_zero {n : ℕ}
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) {F : Space n → Space n}
    (hF : ∀ i : Fin n, ContDiffOn ℝ ∞ (fun x => F x i) Ω)
    (hdivF : ∀ x ∈ Ω, coordinateDivergence F x = 0)
    {φ : Space n → ℝ} (hφ : SmoothTest Ω φ) :
    (∫ x in Ω, inner ℝ (F x) (gradient φ x)) = 0 := by
  have hzero : (fun x => coordinateDivergence F x * φ x) = 0 := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hdivF x hx]
    · have hφx : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => hx (hφ.2.2 ht))
      simp [hφx]
  rw [(integral_inner_gradient_eq_neg_divergence hΩ hF hφ).2.2, hzero]
  simp

/-- A locally smooth, classically divergence-free actual p-flux satisfies
the manuscript's full Sobolev-test weak equation. -/
theorem weakPHarmonicPair_of_divergence_eq_zero {n : ℕ} {p : ℝ}
    (hp : 1 < p) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hSob : LocallySobolevPair p Ω u g)
    (hflux : ∀ i : Fin n, ContDiffOn ℝ ∞ (fun x => pFlux p (g x) i) Ω)
    (hdiv : ∀ x ∈ Ω, coordinateDivergence (fun y => pFlux p (g y)) x = 0) :
    WeakPHarmonicPair p Ω u g := by
  apply weakPHarmonicPair_of_smooth_test_equation hp hΩ hSob
  intro D hD φ hφ
  have hDΩ : D ⊆ Ω := subset_closure.trans hD.2.2
  exact integral_inner_gradient_eq_zero_of_divergence_eq_zero hD.1
    (fun i => (hflux i).mono hDΩ) (fun x hx => hdiv x (hDΩ hx)) hφ

end BMCompactPDE

#print axioms BMCompactPDE.integral_inner_gradient_eq_neg_divergence
#print axioms BMCompactPDE.integral_inner_gradient_eq_zero_of_divergence_eq_zero
#print axioms BMCompactPDE.weakPHarmonicPair_of_divergence_eq_zero
