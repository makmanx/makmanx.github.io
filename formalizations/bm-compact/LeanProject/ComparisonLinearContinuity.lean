import ComparisonLinearGradient

/-! Constructed continuous representatives of the actual weak-gradient field
of a constant-source linear solution, in dimensions n>=3. The components'
actual harmonic weak equations were derived, not assumed. This module does
not yet identify the continuous weak-gradient field with a classical derivative. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

/-- Every supplied actual weak gradient of a linear constant-source Sobolev
solution has a continuous a.e.-equal representative locally, in n>=3.
The scalar Sobolev function itself may still be a raw a.e. representative. -/
theorem WeakPSourcePair.exists_continuous_weak_gradient_two
    {n : ℕ} {c : ℝ} {Ω D : Set (Space n)}
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair 2 c Ω u g) (hf : SobolevPair 2 Ω u g)
    (hn : 3≤n) (hΩb : Bornology.IsBounded Ω) (hD : LocalDomain D Ω) :
    ∃ G : Space n → Space n,∃ H : Fin n → Space n → Space n,
      ContinuousOn G D ∧ g =ᵐ[volume.restrict D] G ∧ SobolevPair 2 D u G ∧
      ∀ i : Fin n,WeakPHarmonicPair 2 D (fun x => G x i) (H i) := by
  classical
  have h2n : (2 : ℝ)<(n : ℝ) := by
    have hh : 2<n := lt_of_lt_of_le (by decide : 2<3) hn
    exact_mod_cast hh
  obtain ⟨H,hH⟩ := hu.exists_weak_harmonic_gradient_rows_two hf hΩb hD
  have hex (i : Fin n) := (hH i).2.source_zero.exists_continuous_weak_representative h2n
  choose v hvc hAE hv using hex
  let G : Space n → Space n := fun x => WithLp.toLp 2 (fun i => v i x)
  have hGc : ContinuousOn G D :=
    (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp_continuousOn
      (continuousOn_pi.mpr hvc)
  have hgG : g =ᵐ[volume.restrict D] G := by
    filter_upwards [eventually_all.mpr hAE] with x hx
    apply PiLp.ext
    intro i
    exact hx i
  refine ⟨G,H,hGc,hgG,(hu.2.2.1 D hD).congr EventuallyEq.rfl hgG,?_⟩
  intro i
  change WeakPHarmonicPair 2 D (v i) (H i)
  exact (hv i).harmonic_of_source_zero

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.exists_continuous_weak_gradient_two
