import RootOscillationSequence

/-! Dependent interval recursion for an explicitly supplied one-step estimate.
The PDE must supply that actual estimate; no decay or continuity is hidden. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology
namespace BMCompactRegularity

theorem exists_decaying_ae_interval_sequence
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) (U : ℕ → Set X) {q : ℝ}
    (hq0 : 0≤q) (hq1 : q<1) (F : ℕ → ℝ)
    (hF : Tendsto F atTop (𝓝 0)) (lo0 hi0 : ℝ) (h0 : lo0≤hi0)
    (hae0 : ∀ᵐ x ∂μ.restrict (U 0),lo0≤u x ∧ u x≤hi0)
    (hstep : ∀ (j : ℕ) (lo hi : ℝ),lo≤hi →
      (∀ᵐ x ∂μ.restrict (U j),lo≤u x ∧ u x≤hi) →
      ∃ lo' hi' : ℝ,lo'≤hi' ∧
        (∀ᵐ x ∂μ.restrict (U (j+1)),lo'≤u x ∧ u x≤hi') ∧
        hi'-lo'≤max (q*(hi-lo)) (F j)) :
    ∃ lo hi : ℕ → ℝ,(∀ j,lo j≤hi j) ∧
      (∀ j,∀ᵐ x ∂μ.restrict (U j),lo j≤u x ∧ u x≤hi j) ∧
      Tendsto (fun j => hi j-lo j) atTop (𝓝 0) := by
  let S : ℕ → Type := fun j => {z : ℝ×ℝ //
    z.1≤z.2 ∧ ∀ᵐ x ∂μ.restrict (U j),z.1≤u x ∧ u x≤z.2}
  have next_exists (j : ℕ) (s : S j) :
      ∃ t : S (j+1),t.1.2-t.1.1≤max (q*(s.1.2-s.1.1)) (F j) := by
    obtain ⟨lo,hi,hle,hae,hwidth⟩ := hstep j s.1.1 s.1.2 s.2.1 s.2.2
    exact ⟨⟨(lo,hi),hle,hae⟩,hwidth⟩
  let next : (j : ℕ) → S j → S (j+1) := fun j s =>
    Classical.choose (next_exists j s)
  let initial : S 0 := ⟨(lo0,hi0),h0,hae0⟩
  let seq : (j : ℕ) → S j := fun j => Nat.rec (motive := S) initial next j
  let lo : ℕ → ℝ := fun j => (seq j).1.1
  let hi : ℕ → ℝ := fun j => (seq j).1.2
  have hord (j : ℕ) : lo j≤hi j := (seq j).2.1
  have hdec (j : ℕ) : hi (j+1)-lo (j+1)≤max (q*(hi j-lo j)) (F j) := by
    exact Classical.choose_spec (next_exists j (seq j))
  refine ⟨lo,hi,hord,fun j => (seq j).2.2,?_⟩
  exact tendsto_zero_of_max_contraction hq0 hq1
    (fun j => sub_nonneg.mpr (hord j)) hF hdec

end BMCompactRegularity
#print axioms BMCompactRegularity.exists_decaying_ae_interval_sequence
