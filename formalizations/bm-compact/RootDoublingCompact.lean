import BMCompactCriticalChecked
import Mathlib.Topology.Compactness.Compact

/-! Actual compact doubling localization. A directed open cover of the bad
boundary set supplies one penalty coefficient making every positive doubled
maximum interior. No existence or interior location of a maximizing pair is
assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace BMCompactPDE

theorem compact_penalty_separates_bad_set {X : Type*} [TopologicalSpace X]
    {B : Set X} (hB : IsCompact B) {f P : X → ℝ}
    (hf : UpperSemicontinuous f) (hP : Continuous P) (hP0 : ∀ x,0≤P x)
    (hz : ∀ x∈B,P x=0 → f x≤0) {η : ℝ} (hη : 0<η) :
    ∃ j : ℕ, ∀ x∈B, f x-(j : ℝ)*P x<η := by
  let U : ℕ → Set X := fun j=>{x | f x-(j : ℝ)*P x<η}
  have hU (j : ℕ) : IsOpen (U j) := by
    have hc : Continuous (fun x=>(j : ℝ)*P x) := continuous_const.mul hP
    have hu : UpperSemicontinuous (fun x=>f x-(j : ℝ)*P x) := hf.add hc.neg.upperSemicontinuous
    exact hu.isOpen_preimage η
  have hcover : B ⊆ ⋃ j,U j := by
    intro x hx
    by_cases hp : P x=0
    · refine mem_iUnion.mpr ⟨0,?_⟩
      change f x-((0 : ℕ) : ℝ)*P x<η
      simpa only [Nat.cast_zero,zero_mul,sub_zero] using (hz x hx hp).trans_lt hη
    · have hpp : 0<P x := lt_of_le_of_ne (hP0 x) (Ne.symm hp)
      obtain ⟨j,hj⟩ := exists_nat_gt ((f x-η)/(P x))
      refine mem_iUnion.mpr ⟨j,?_⟩
      have hh := (div_lt_iff₀ hpp).mp hj
      change f x-(j : ℝ)*P x<η
      linarith
  have hmono {i j : ℕ} (hij : i≤j) : U i ⊆ U j := by
    intro x hx
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij : (i : ℝ)≤j) (hP0 x)
    change f x-(i : ℝ)*P x<η at hx
    change f x-(j : ℝ)*P x<η
    linarith
  obtain ⟨j,hj⟩ := hB.elim_directed_cover U hU hcover
    (fun a b=>⟨max a b,hmono (le_max_left _ _),hmono (le_max_right _ _)⟩)
  exact ⟨j,hj⟩

theorem exists_penalized_maximum_off_bad_set {X : Type*} [TopologicalSpace X]
    [CompactSpace X] {B : Set X} (hB : IsClosed B) {f P : X → ℝ}
    (hf : UpperSemicontinuous f) (hP : Continuous P) (hP0 : ∀ x,0≤P x)
    (hz : ∀ x∈B,P x=0 → f x≤0) (x₀ : X) (hxP : P x₀=0) (hxF : 0<f x₀) :
    ∃ j : ℕ, 0<j ∧ ∃ z : X, z∉B ∧ 0<f z-(j : ℝ)*P z ∧
      ∀ w : X, f w-(j : ℝ)*P w≤f z-(j : ℝ)*P z := by
  obtain ⟨j,hj⟩ := compact_penalty_separates_bad_set hB.isCompact hf hP hP0 hz hxF
  let J : ℕ := j+1
  have hjJ (z : X) (hzB : z∈B) : f z-(J : ℝ)*P z<f x₀ := by
    have hle : (j : ℝ)≤(J : ℝ) := by dsimp only [J];push_cast;linarith
    have hp := mul_le_mul_of_nonneg_right hle (hP0 z)
    have hold := hj z hzB
    linarith
  have hu : UpperSemicontinuous (fun z=>f z-(J : ℝ)*P z) :=
    hf.add ((continuous_const.mul hP).neg.upperSemicontinuous)
  obtain ⟨z,_,hm⟩ := UpperSemicontinuousOn.exists_isMaxOn ⟨x₀,mem_univ _⟩
    isCompact_univ (hu.upperSemicontinuousOn univ)
  have hh := hm (mem_univ x₀)
  change f x₀-(J : ℝ)*P x₀≤f z-(J : ℝ)*P z at hh
  rw [hxP,mul_zero,sub_zero] at hh
  refine ⟨J,by dsimp only [J];omega,z,?_,hxF.trans_le hh,fun w=>hm (mem_univ w)⟩
  intro hzB
  exact (not_lt_of_ge hh) (hjJ z hzB)

/-- For an actual positive diagonal gap, the genuine norm-power doubled
objective has an attained positive maximum with BOTH coordinates interior. -/
theorem exists_interior_doubled_power_maximum {n : ℕ} {D : Set (Space n)}
    (hD : IsOpen D) (hDb : Bornology.IsBounded D) {u v : Space n → ℝ}
    (hu : UpperSemicontinuousOn u (closure D)) (hv : ContinuousOn v (closure D))
    (hb : ∀ x∈frontier D,u x≤v x) {a : Space n} (ha : a∈D) (hgap : 0<u a-v a)
    {q : ℝ} (hq : 1<q) :
    ∃ j : ℕ, 0<j ∧ ∃ x∈D, ∃ y∈D,
      0<u x-v y-(j : ℝ)*criticalPowerPenalty q (x-y) ∧
      ∀ z∈closure D, ∀ w∈closure D,
        u z-v w-(j : ℝ)*criticalPowerPenalty q (z-w) ≤
          u x-v y-(j : ℝ)*criticalPowerPenalty q (x-y) := by
  let K := closure D
  let X := ↥K × ↥K
  letI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hDb.isCompact_closure
  let f : X → ℝ := fun z=>u z.1-v z.2
  let P : X → ℝ := fun z=>criticalPowerPenalty q ((z.1 : Space n)-z.2)
  let B : Set X := {z | (z.1 : Space n)∈frontier D ∨ (z.2 : Space n)∈frontier D}
  have hB : IsClosed B :=
    (isClosed_frontier.preimage (continuous_subtype_val.comp continuous_fst)).union
      (isClosed_frontier.preimage (continuous_subtype_val.comp continuous_snd))
  have huK : UpperSemicontinuous (fun z : ↥K=>u z) :=
    upperSemicontinuousOn_iff_restrict.mpr hu
  have hvK : Continuous (fun z : ↥K=>v z) := continuousOn_iff_continuous_domRestrict.mp hv
  have hf : UpperSemicontinuous f :=
    (huK.comp continuous_fst).add (hvK.comp continuous_snd).neg.upperSemicontinuous
  have hd : Differentiable ℝ (criticalPowerPenalty q : Space n → ℝ) :=
    fun x=>(hasGradientAt_criticalPowerPenalty hq x).differentiableAt
  have hPc : Continuous (criticalPowerPenalty q : Space n → ℝ) := hd.continuous
  have hP : Continuous P := hPc.comp
    ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd))
  have hq0 : 0<q := zero_lt_one.trans hq
  have hP0 (z : X) : 0≤P z :=
    mul_nonneg (inv_nonneg.mpr hq0.le) (Real.rpow_nonneg (norm_nonneg _) _)
  have hz : ∀ z∈B,P z=0 → f z≤0 := by
    intro z hz hp
    have he : (z.1 : Space n)=(z.2 : Space n) := by
      by_contra hn
      have hp' := criticalPowerPenalty_pos_of_ne_zero hq0 (sub_ne_zero.mpr hn)
      exact (ne_of_gt hp') hp
    rcases hz with hleft | hright
    · simpa only [f,he,sub_nonpos] using hb (z.1 : Space n) hleft
    · simpa only [f,he,sub_nonpos] using hb (z.2 : Space n) hright
  let aK : ↥K := ⟨a,subset_closure ha⟩
  have haP : P (aK,aK)=0 := by simp [P,aK,criticalPowerPenalty,Real.zero_rpow hq0.ne']
  obtain ⟨j,hjpos,z,hzB,hpos,hm⟩ := exists_penalized_maximum_off_bad_set hB hf hP hP0 hz
    (aK,aK) haP hgap
  have hx : (z.1 : Space n)∈D := by
    by_contra hn
    apply hzB
    left
    rw [hD.frontier_eq]
    exact ⟨z.1.property,hn⟩
  have hy : (z.2 : Space n)∈D := by
    by_contra hn
    apply hzB
    right
    rw [hD.frontier_eq]
    exact ⟨z.2.property,hn⟩
  refine ⟨j,hjpos,z.1,hx,z.2,hy,hpos,?_⟩
  intro w hw y hy
  exact hm (⟨w,hw⟩,⟨y,hy⟩)

end BMCompactPDE
#print axioms BMCompactPDE.compact_penalty_separates_bad_set
#print axioms BMCompactPDE.exists_penalized_maximum_off_bad_set
#print axioms BMCompactPDE.exists_interior_doubled_power_maximum
