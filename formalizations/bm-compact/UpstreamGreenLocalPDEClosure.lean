import UpstreamGreenStrongClosure

/-! Actual weak-PDE closure on cofinal bounded interior windows. The true
strong Lp convergence and eventual equations are explicit inputs; the SAME
limiting gradient and full local W0 PDE are constructed, not assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace BMCompactPDE

theorem weakPHarmonicPair_of_cofinal_local_strong_Lp_limits
    {n : ℕ} {p : ℝ} (hp : 1<p) {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {D : ℕ → Set (Space n)} (hD : ∀ m,LocalDomain (D m) Ω)
    (hcofinal : ∀ E : Set (Space n),LocalDomain E Ω → ∃ m,closure E⊆D m)
    {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n}
    {v : Space n → ℝ} {h : Space n → Space n}
    (hSob : ∀ j m,SobolevPair p (D m) (u j) (g j))
    (hPDE : ∀ m,∀ᶠ j in atTop,WeakPHarmonicPair p (D m) (u j) (g j))
    (hv : ∀ m,MemLp v (ENNReal.ofReal p) (volume.restrict (D m)))
    (hh : ∀ m,MemLp h (ENNReal.ofReal p) (volume.restrict (D m)))
    (hlimu : ∀ m,Tendsto (fun j=>eLpNorm (u j-v) (ENNReal.ofReal p)
      (volume.restrict (D m))) atTop (𝓝 0))
    (hlimg : ∀ m,Tendsto (fun j=>eLpNorm (g j-h) (ENNReal.ofReal p)
      (volume.restrict (D m))) atTop (𝓝 0)) :
    WeakPHarmonicPair p Ω v h := by
  have hlocal (m : ℕ) : SobolevPair p (D m) v h ∧ WeakPHarmonicPair p (D m) v h := by
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hPDE m)
    exact weakPHarmonicPair_of_actual_strong_Lp_limits hp (hD m).1 (hD m).2.1
      (fun j=>hSob (j+N) m) (fun j=>hN (j+N) (Nat.le_add_left N j))
      (hv m) (hh m) ((hlimu m).comp (tendsto_add_atTop_nat N))
      ((hlimg m).comp (tendsto_add_atTop_nat N))
  refine ⟨hp,hΩ,?_,?_⟩
  · intro E hE
    obtain ⟨m,hm⟩ := hcofinal E hE
    exact (hlocal m).1.mono_actual (subset_closure.trans hm)
  · intro E hE θ k hθ
    obtain ⟨m,hm⟩ := hcofinal E hE
    exact (hlocal m).2.2.2.2 E ⟨hE.1,hE.2.1,hm⟩ θ k hθ

end BMCompactPDE
#print axioms BMCompactPDE.weakPHarmonicPair_of_cofinal_local_strong_Lp_limits
