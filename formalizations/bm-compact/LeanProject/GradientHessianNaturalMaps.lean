import GradientHessianUniformApproximation

/-! The natural gradient transform and its genuine quantitative map bounds.
These are operator/integrability statements, not pointwise gradient regularity. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

def naturalGradientMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p ε : ℝ) (v : E) : E := (ε^2+‖v‖^2)^((p-2)/4) • v

theorem continuous_naturalGradientMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ} (hp : 2≤p) (ε : ℝ) : Continuous (naturalGradientMap (E:=E) p ε) := by
  exact ((continuous_const.add (continuous_norm.pow 2)).rpow_const
    (fun _ => Or.inr (by linarith : 0≤(p-2)/4))).smul continuous_id

private theorem naturalGradientMap_weight_square (p ε M : ℝ) :
    ((ε^2+M^2)^((p-2)/4))^2=(ε^2+M^2)^((p-2)/2) := by
  rw [←Real.rpow_two,←Real.rpow_mul (add_nonneg (sq_nonneg ε) (sq_nonneg M))]
  congr 1
  ring

theorem norm_naturalGradientMap_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p ε : ℝ) (v : E) :
    ‖naturalGradientMap p ε v‖^2=(ε^2+‖v‖^2)^((p-2)/2)*‖v‖^2 := by
  rw [naturalGradientMap,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (add_nonneg (sq_nonneg ε) (sq_nonneg ‖v‖)) _),
    mul_pow,naturalGradientMap_weight_square]

theorem naturalGradientMap_difference_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {p ε : ℝ} (hp : 2≤p) (hε : ε≠0) (v w : E) :
    ‖naturalGradientMap p ε v-naturalGradientMap p ε w‖^2≤
      (p/2)^2*(ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/2)*‖v-w‖^2 := by
  let q : ℝ := (p+2)/2
  have hq : 2≤q := by dsimp only [q];linarith
  have hq1 : q-1=p/2 := by dsimp only [q];ring
  have hq2 : (q-2)/2=(p-2)/4 := by dsimp only [q];ring
  have hd := regularized_pFlux_difference_norm_le_ge_two hq hε v w
  simp only [hq1,hq2] at hd
  change ‖naturalGradientMap p ε v-naturalGradientMap p ε w‖≤
    (p/2)*(ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/4)*‖v-w‖ at hd
  have hN : 0≤(p/2)*(ε^2+(max ‖v‖ ‖w‖)^2)^((p-2)/4)*‖v-w‖ := by
    apply mul_nonneg (mul_nonneg (by linarith)
      (Real.rpow_nonneg (add_nonneg (sq_nonneg ε) (sq_nonneg _)) _)) (norm_nonneg _)
  have hs := (sq_le_sq₀ (norm_nonneg _) hN).mpr hd
  simpa only [mul_pow,naturalGradientMap_weight_square] using hs

theorem memLp_naturalGradientMap {n : ℕ} {p ε : ℝ} (hp : 2≤p)
    {μ : Measure (Space n)} [IsFiniteMeasure μ] {g : Space n → Space n}
    (hg : MemLp g (ENNReal.ofReal p) μ) :
    MemLp (fun x => naturalGradientMap p ε (g x)) 2 μ := by
  have hI := integrable_regularized_weighted_square (ε:=ε) hp hg hg hg.norm
  have he : (fun x => (ε^2+(max ‖g x‖ ‖g x‖)^2)^((p-2)/2)*‖‖g x‖‖^2)=
      (fun x => ‖naturalGradientMap p ε (g x)‖^2) := by
    funext x
    simp only [norm_naturalGradientMap_sq,max_self,Real.norm_eq_abs,abs_norm]
  rw [he] at hI
  exact (memLp_two_iff_integrable_sq_norm
    ((continuous_naturalGradientMap hp ε).comp_aestronglyMeasurable hg.1)).mpr hI

end BMCompactPDE
#print axioms BMCompactPDE.continuous_naturalGradientMap
#print axioms BMCompactPDE.norm_naturalGradientMap_sq
#print axioms BMCompactPDE.naturalGradientMap_difference_sq_le
#print axioms BMCompactPDE.memLp_naturalGradientMap
