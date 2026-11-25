import CapacityNaturalHolder

/-! The refined Holder estimate for the actual regularized PDE weight.
The difference norm remains a separate squared small factor; no gradient
bound, Hessian, desired energy estimate or classical regularity is input. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

private theorem capacity_natural_regularized_weight_le {n : ℕ} {p : ℝ}
    (hp : 2≤p) (ε : ℝ) (v w : Space n) :
    (ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2)≤(|ε|+‖v‖+‖w‖)^(p-2) := by
  let H : ℝ := |ε|+‖v‖+‖w‖
  have hH : 0≤H := by dsimp only [H];positivity
  have hM0 : 0≤max ‖v‖ ‖w‖ := (norm_nonneg _).trans (le_max_left _ _)
  have hMle : max ‖v‖ ‖w‖≤‖v‖+‖w‖ := max_le
    (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  have hs : Real.sqrt (ε^2+(max ‖v‖ ‖w‖)^2)≤H := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨hH,?_⟩
    have hsq : ε^2+(max ‖v‖ ‖w‖)^2≤(|ε|+max ‖v‖ ‖w‖)^2 := by
      nlinarith only [mul_nonneg (abs_nonneg ε) hM0,sq_abs ε]
    exact hsq.trans ((sq_le_sq₀ (add_nonneg (abs_nonneg _) hM0) hH).mpr
      (by dsimp only [H];linarith only [hMle]))
  have hW := Real.rpow_le_rpow (Real.sqrt_nonneg _) hs (sub_nonneg.mpr hp)
  have he : (Real.sqrt (ε^2+(max ‖v‖ ‖w‖)^2))^(p-2)=
      (ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (add_nonneg (sq_nonneg ε) (sq_nonneg _))]
    congr 1
    ring
  rw [he] at hW
  exact hW

set_option maxHeartbeats 1000000 in
theorem regularized_weighted_square_refined_holder_bound {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {p ε : ℝ} (hp : 2≤p)
    {μ : Measure (Space n)} [IsFiniteMeasure μ]
    {g h : Space n → Space n} {z : Space n → E}
    (hg : MemLp g (ENNReal.ofReal p) μ) (hh : MemLp h (ENNReal.ofReal p) μ)
    (hz : MemLp z (ENNReal.ofReal p) μ) :
    Integrable (fun x => (ε^2+(max ‖g x‖ ‖h x‖)^2)^((p-2)/2)*‖z x‖^2) μ ∧
      (∫ x,(ε^2+(max ‖g x‖ ‖h x‖)^2)^((p-2)/2)*‖z x‖^2 ∂μ)≤
        ((eLpNorm (fun _ : Space n => |ε|) (ENNReal.ofReal p) μ).toReal+
          (eLpNorm g (ENNReal.ofReal p) μ).toReal+
          (eLpNorm h (ENNReal.ofReal p) μ).toReal)^(p-2)*
            (eLpNorm z (ENNReal.ofReal p) μ).toReal^2 := by
  have hp1 : 1≤p := by linarith
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp1⟩
  let H : Space n → ℝ := fun x => |ε|+‖g x‖+‖h x‖
  have hH0 (x : Space n) : 0≤H x := by dsimp only [H];positivity
  have hc : MemLp (fun _ : Space n => |ε|) (ENNReal.ofReal p) μ := memLp_const |ε|
  have hHm : MemLp H (ENNReal.ofReal p) μ := by
    simpa only [H,Pi.add_apply] using! (hc.add hg.norm).add hh.norm
  obtain ⟨hHi,hHb⟩ := weighted_square_refined_holder_bound hp hH0 hHm hz
  have hi : Integrable (fun x => (ε^2+(max ‖g x‖ ‖h x‖)^2)^((p-2)/2)*‖z x‖^2) μ := by
    simpa only [norm_norm] using integrable_regularized_weighted_square hp hg hh hz.norm
  have hmono := integral_mono hi hHi (fun x =>
    mul_le_mul_of_nonneg_right (capacity_natural_regularized_weight_le hp ε (g x) (h x)) (sq_nonneg ‖z x‖))
  let C := hc.toLp (fun _ : Space n => |ε|)
  let G := hg.norm.toLp (fun x => ‖g x‖)
  let J := hh.norm.toLp (fun x => ‖h x‖)
  let V := C+G+J
  have hAE : V=ᵐ[μ] H := by
    filter_upwards [Lp.coeFn_add (C+G) J,Lp.coeFn_add C G,
      hc.coeFn_toLp,hg.norm.coeFn_toLp,hh.norm.coeFn_toLp] with x ha hb hC hG hJ
    change (C+G+J : Lp ℝ (ENNReal.ofReal p) μ) x=_
    rw [ha,Pi.add_apply,hb,Pi.add_apply,hC,hG,hJ]
  have hVN : ‖V‖=(eLpNorm H (ENNReal.ofReal p) μ).toReal := by
    rw [Lp.norm_def,eLpNorm_congr_ae hAE]
  have hVbound : (eLpNorm H (ENNReal.ofReal p) μ).toReal≤
      (eLpNorm (fun _ : Space n => |ε|) (ENNReal.ofReal p) μ).toReal+
        (eLpNorm g (ENNReal.ofReal p) μ).toReal+
        (eLpNorm h (ENNReal.ofReal p) μ).toReal := by
    have ht : ‖V‖≤‖C‖+‖G‖+‖J‖ :=
      (norm_add_le (C+G) J).trans (add_le_add (norm_add_le C G) le_rfl)
    simpa only [hVN,C,G,J,Lp.norm_toLp,eLpNorm_norm] using ht
  refine ⟨hi,(hmono.trans hHb).trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow ENNReal.toReal_nonneg hVbound (sub_nonneg.mpr hp)) (sq_nonneg _)

end BMCompactPDE
#print axioms BMCompactPDE.regularized_weighted_square_refined_holder_bound
