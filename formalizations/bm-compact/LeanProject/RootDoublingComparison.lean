import RootDoublingCompact
import ContactClassicalForce
import PropagationTranslationCalculus

/-! Critical comparison by actual compact doubling and diagonal translation.
The comparator may have critical points. Its actual differentiability and C2
regularity at noncritical points are explicit; no general regularity or forced
solution existence theorem is silently supplied. No theorem on sums is used. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ContDiff
namespace BMCompactPDE

private theorem penalty_sub_comm {n : ℕ} (q : ℝ) (x y : Space n) :
    criticalPowerPenalty q (x-y)=criticalPowerPenalty q (y-x) := by
  unfold criticalPowerPenalty
  rw [norm_sub_rev x y]

theorem gradient_ne_zero_at_doubled_maximum {n : ℕ} {D : Set (Space n)}
    (hD : IsOpen D) {u v : Space n → ℝ} {q j : ℝ} (hq : 1<q) (hj : j≠0)
    {x y : Space n} (hx : x∈D) (hy : y∈D) (hxy : x≠y)
    (hvd : DifferentiableAt ℝ v y)
    (hm : ∀ z∈D, ∀ w∈D,
      u z-v w-j*criticalPowerPenalty q (z-w) ≤
        u x-v y-j*criticalPowerPenalty q (x-y)) : gradient v y≠0 := by
  let A := v y+j*criticalPowerPenalty q (y-x)
  let ψ := flatContactPower q j A x
  have hψd : DifferentiableAt ℝ ψ y :=
    (contDiff_one_flatContactPower hq j A x).differentiable (by norm_num) y
  have hψy : ψ y=v y := by
    dsimp only [ψ,flatContactPower,A]
    ring
  have hbelow : ∀ᶠ z in 𝓝 y, ψ z≤v z := by
    filter_upwards [hD.mem_nhds hy] with z hz
    have hh := hm x hx z hz
    rw [penalty_sub_comm q x z,penalty_sub_comm q x y] at hh
    dsimp only [ψ,flatContactPower,A]
    linarith
  have he := BMCompactAnalytic.gradient_eq_of_local_upper_contact hψd hvd hψy hbelow
  have hgψ : gradient ψ y≠0 := by
    change gradient (flatContactPower q j A x) y≠0
    rw [gradient_flatContactPower hq]
    exact smul_ne_zero (neg_ne_zero.mpr hj)
      (gradient_criticalPowerPenalty_ne_zero hq (sub_ne_zero.mpr hxy.symm))
  rw [←he]
  exact hgψ

theorem diagonal_upper_test_of_doubled_maximum {n : ℕ} {D : Set (Space n)}
    (hD : IsOpen D) {u v : Space n → ℝ} {q j : ℝ}
    {x y : Space n} (hx : x∈D) (hy : y∈D)
    (hm : ∀ z∈D, ∀ w∈D,
      u z-v w-j*criticalPowerPenalty q (z-w) ≤
        u x-v y-j*criticalPowerPenalty q (x-y)) :
    u x=(fun z=>v (z+y-x)+(u x-v y)) x ∧
      ∀ᶠ z in 𝓝 x, u z≤v (z+y-x)+(u x-v y) := by
  have hshift : x+y-x=y := by abel
  refine ⟨?_,?_⟩
  · change u x=v (x+y-x)+(u x-v y)
    rw [hshift]
    ring
  · have hT : Continuous (fun z : Space n=>z+y-x) :=
      (continuous_id.add continuous_const).sub continuous_const
    have hDy : ∀ᶠ w in 𝓝 y,w∈D := by
      filter_upwards [hD.mem_nhds hy] with w hw
      exact hw
    have hTe : Tendsto (fun z : Space n=>z+y-x) (𝓝 x) (𝓝 y) := by
      simpa only [hshift] using (hT.continuousAt (x := x)).tendsto
    have hNy : ∀ᶠ z in 𝓝 x,z+y-x∈D := hTe.eventually hDy
    filter_upwards [hD.mem_nhds hx,hNy] with z hz hzy
    have hh := hm z hz (z+y-x) hzy
    have he : z-(z+y-x)=x-y := by abel
    rw [he] at hh
    linarith

/-- Genuine comparison with positive-source weak supersolutions, permitting
arbitrary critical points. The regularity of this actual comparator remains
explicit: differentiable on its domain, C2 only at noncritical points. -/
theorem WeakPSourceSupersolutionPair.viscosity_le_of_noncritical_reg
    {n : ℕ} {p c : ℝ} {Ω D : Set (Space n)} {u v : Space n → ℝ}
    {g : Space n → Space n} (hv : WeakPSourceSupersolutionPair p c Ω v g)
    (hc : 0<c) (hvc : ContinuousOn v Ω) (hvd : DifferentiableOn ℝ v Ω)
    (hv2 : ∀ z∈Ω, gradient v z≠0 → ContDiffAt ℝ 2 v z)
    (hu : BMCompactAnalytic.IsViscosityPSubsolution p Ω u)
    (hn : 2≤n) (hD : LocalDomain D Ω) (hb : ∀ z∈frontier D,u z≤v z) :
    ∀ z∈D,u z≤v z := by
  intro a ha
  by_contra hnot
  have hgap : 0<u a-v a := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨k,hk,hs⟩ := exists_even_flat_contact_exponent hv.1
  let q : ℝ := ((2*k : ℕ) : ℝ)
  have hq : 1<q := by
    have hh : (2 : ℝ)≤(k : ℝ) := by exact_mod_cast hk
    dsimp only [q]
    push_cast
    linarith
  have hDΩ : D ⊆ Ω := subset_closure.trans hD.2.2
  obtain ⟨j,hj,x,hx,y,hy,hpos,hm⟩ := exists_interior_doubled_power_maximum hD.1 hD.2.1
    (hu.2.2.1.mono hD.2.2) (hvc.mono hD.2.2) hb ha hgap hq
  have hmD : ∀ z∈D,∀ w∈D,
      u z-v w-(j : ℝ)*criticalPowerPenalty q (z-w) ≤
        u x-v y-(j : ℝ)*criticalPowerPenalty q (x-y) :=
    fun z hz w hw=>hm z (subset_closure hz) w (subset_closure hw)
  have hxy := (hv.mono hDΩ hD.1).ne_of_doubled_maximum hc (hvc.mono hDΩ) hn hq hs
    u (j : ℝ) hx hy hmD
  have hj0 : (j : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hyd : DifferentiableAt ℝ v y :=
    (hvd y (hDΩ hy)).differentiableAt (hv.2.1.mem_nhds (hDΩ hy))
  have hgy := gradient_ne_zero_at_doubled_maximum hD.1 hq hj0 hx hy hxy hyd hmD
  have hy2 := hv2 y (hDΩ hy) hgy
  let φ : Space n → ℝ := fun z=>v (z+y-x)+(u x-v y)
  have hφ2 : ContDiffAt ℝ 2 φ x :=
    BMCompactAnalytic.contDiffAt_diagonal_translate_add_const hy2 (u x-v y)
  obtain ⟨hφx,hupper⟩ := diagonal_upper_test_of_doubled_maximum hD.1 hx hy hmD
  have hφg : gradient φ x≠0 := by
    change gradient (fun z=>v (z+y-x)+(u x-v y)) x≠0
    rw [BMCompactAnalytic.gradient_diagonal_translate_add_const]
    exact hgy
  have huP := hu.2.2.2 x (hDΩ hx) φ hφ2 hφx hupper hφg
  have hvP := hv.normalizedPLaplacian_neg_of_contDiffAt_two hc hn (hDΩ hy) hy2 hgy
  change 0≤BMCompactAnalytic.normalizedPLaplacian p
    (fun z=>v (z+y-x)+(u x-v y)) x at huP
  rw [BMCompactAnalytic.normalizedPLaplacian_diagonal_translate_add_const] at huP
  exact (not_le_of_gt hvP) huP

end BMCompactPDE
#print axioms BMCompactPDE.gradient_ne_zero_at_doubled_maximum
#print axioms BMCompactPDE.diagonal_upper_test_of_doubled_maximum
#print axioms BMCompactPDE.WeakPSourceSupersolutionPair.viscosity_le_of_noncritical_reg
