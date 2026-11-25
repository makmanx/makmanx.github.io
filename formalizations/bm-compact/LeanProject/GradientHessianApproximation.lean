import GradientHessianActual
import RootForcedRegularization

/-! Construct actual fixed-source regularized W1,p approximants with genuine
local W1,2 gradient rows, p>=2. The approximants, strong convergence and each
weak Hessian are derived. Neither smoothness nor epsilon-uniform H2 is asserted. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace BMCompactPDE

theorem WeakPSourcePair.exists_regularized_source_W1p_approximants_with_weak_hessian
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hH : WeakPSourcePair p c Ω f gf) (hf : SobolevPair p Ω f gf)
    (hp : 2≤p) (hn : 2≤n) (hΩb : Bornology.IsBounded Ω) :
    ∃ w : ℕ → Space n → ℝ,∃ gw : ℕ → Space n → Space n,
      (∀ j,ZeroBoundarySobolevPair p Ω (w j) (gw j)) ∧
      (∀ j : ℕ,GlobalWeakRegularizedSourcePair p (((j:ℝ)+1)⁻¹) c Ω (f+w j) (gf+gw j)) ∧
      (∀ j : ℕ,∀ D : Set (Space n),LocalDomain D Ω →
        ∃ H : Fin n → Space n → Space n,
          ∀ i : Fin n,SobolevPair 2 D (fun x => (gf+gw j) x i) (H i)) ∧
      Tendsto (fun j=>eLpNorm (gw j) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) ∧
      Tendsto (fun j=>eLpNorm (w j) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) := by
  obtain ⟨w,gw,hw,hu,hg,hwlim⟩ := hH.exists_regularized_source_W1p_approximants hf hn hΩb
  refine ⟨w,gw,hw,hu,?_,hg,hwlim⟩
  intro j D hD
  apply (hu j).exists_local_sobolev_gradient_rows_ge_two hp _ hΩb hD
  exact inv_ne_zero (by positivity : (j:ℝ)+1≠0)

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.exists_regularized_source_W1p_approximants_with_weak_hessian
