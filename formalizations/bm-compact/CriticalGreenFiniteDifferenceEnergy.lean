import CriticalGreenDifferenceWindow

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal
namespace BMCompactPDE

/-- On a full exterior tail the actual gradient difference from the logarithmic
fundamental profile has finite n-energy. Its tail energy tends to zero. -/
theorem WeakPHarmonicPair.finite_critical_green_gradient_difference_energy
    {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0<σ) {K : Set (Space n)} (hK : IsCompact K)
    {u : Space n → ℝ} {g : Space n → Space n} (hu : WeakPHarmonicPair (n:ℝ) Kᶜ u g)
    (hrem : HasBoundedGreenRemainder n σ n u) :
    (∃ r : ℝ, 0<r ∧ IntegrableOn (fun x=>‖g x-gradient (fundamentalPotential n σ n) x‖^n)
      {x | r < ‖x‖} volume) ∧
    Tendsto (fun r : ℝ=>∫ x in {x | r < ‖x‖}, ‖g x-gradient (fundamentalPotential n σ n) x‖^n)
      atTop (𝓝 0) := by
  obtain ⟨S,C,hS,_,hC⟩ := hu.uniform_critical_green_difference_windows hn hσ hK hrem
  let Z := fun x : Space n => ‖(1/2:ℝ) • (g x-gradient (fundamentalPotential n σ n) x)‖^n
  let D := fun j : ℕ => radialAnnulusAt n 0 (4*S) (2*(2*S+j))
  have hwin (j : ℕ) : IntegrableOn Z (D j) volume ∧ ∫ x in D j,Z x ≤ C :=
    hC (2*S+j) (le_add_of_nonneg_right (Nat.cast_nonneg j))
  have hmono : Monotone D := by
    intro i j hij x hx
    have hh : (i:ℝ) ≤ j := by exact_mod_cast hij
    exact ⟨hx.1,hx.2.trans_le (by linarith only [hh])⟩
  have hcover : ⋃ j,D j = {x : Space n | 4*S < ‖x‖} := by
    ext x
    constructor
    · rintro ⟨_,⟨j,rfl⟩,hx⟩
      change 4*S < ‖x‖
      simpa only [dist_zero_right] using hx.1
    · intro hx
      obtain ⟨j,hj⟩ := exists_nat_gt ‖x‖
      apply mem_iUnion.mpr
      refine ⟨j,?_⟩
      change 4*S < dist x 0 ∧ dist x 0 < 2*(2*S+(j:ℝ))
      rw [dist_zero_right]
      exact ⟨hx,by linarith only [hj,hS,Nat.cast_nonneg (α:=ℝ) j]⟩
  have hnonneg (x : Space n) : 0 ≤ Z x := pow_nonneg (norm_nonneg _) _
  have hZI : IntegrableOn Z (⋃ j,D j) volume := by
    refine ⟨AEStronglyMeasurable.iUnion (fun j=>(hwin j).1.1),?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnonneg)).mpr
    rw [setLIntegral_iUnion_of_directed (fun x=>ENNReal.ofReal (Z x)) hmono.directed_le]
    apply lt_of_le_of_lt _ (ENNReal.ofReal_lt_top (r:=C))
    apply iSup_le
    intro j
    rw [←ofReal_integral_eq_lintegral_ofReal (hwin j).1 (Eventually.of_forall hnonneg)]
    exact ENNReal.ofReal_le_ofReal (hwin j).2
  rw [hcover] at hZI
  let f := fun x : Space n => ‖g x-gradient (fundamentalPotential n σ n) x‖^n
  have hraw : IntegrableOn f {x : Space n | 4*S < ‖x‖} volume := by
    have heq : (fun x : Space n => (2:ℝ)^n * Z x) = f := by
      funext x
      dsimp only [Z,f]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),mul_pow,
        ←mul_assoc,←mul_pow]
      norm_num
    exact heq ▸ hZI.const_mul ((2:ℝ)^n)
  refine ⟨⟨4*S,by positivity,hraw⟩,?_⟩
  let T := fun r : ℝ=> {x : Space n | r < ‖x‖}
  have he : ⋂ r,T r = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact lt_irrefl ‖x‖ (mem_iInter.mp hx ‖x‖)
  have ht := tendsto_setIntegral_of_antitone (f:=f) (μ:=volume) (s:=T)
    (fun r=>(isOpen_lt continuous_const continuous_norm).measurableSet)
    (fun i j hij x hx=>lt_of_le_of_lt hij hx) ⟨4*S,hraw⟩
  simpa only [he,setIntegral_empty] using ht

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.finite_critical_green_gradient_difference_energy
