import GradientHessianUniformWeighted

/-! Actual constructed regularized approximants with a common weighted gradient
quotient bound, independent of both epsilon index and quotient length. The scalar
and gradient Lp ceilings follow from proved strong W1,p convergence. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem hessian_uniform_norm_of_strong_corrections
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {P : ℝ≥0∞} (hP : 1≤P)
    {f : α → F} {w : ℕ → α → F} (hf : MemLp f P μ) (hw : ∀ j,MemLp (w j) P μ)
    (hlim : Tendsto (fun j => eLpNorm (w j) P μ) atTop (𝓝 0)) :
    ∃ N : ℝ,0≤N ∧ ∀ j,(eLpNorm (f+w j) P μ).toReal≤N := by
  have ht : Tendsto (fun j => (eLpNorm (w j) P μ).toReal) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero,Function.comp_def] using
      (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞)≠(∞:ℝ≥0∞))).tendsto.comp hlim
  obtain ⟨A,hA,hAb⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_pos_norm_le
  refine ⟨(eLpNorm f P μ).toReal+A,add_nonneg ENNReal.toReal_nonneg hA.le,?_⟩
  intro j
  have hwN : (eLpNorm (w j) P μ).toReal≤A := by
    have hb := hAb ((eLpNorm (w j) P μ).toReal) (mem_range_self j)
    simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using hb
  have hs := eLpNorm_add_le hf.1 (hw j).1 hP
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top,(hw j).eLpNorm_ne_top⟩) hs
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top (hw j).eLpNorm_ne_top] at hr
  linarith only [hr,hwN]

theorem WeakPSourcePair.exists_regularized_source_approximants_uniform_weighted_quotients
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
      (∀ η : Space n → ℝ,SmoothTest Ω η → (∀ x,0≤η x) →
        ∃ δ M : ℝ,0<δ ∧ 0≤M ∧ ∀ j : ℕ,∀ a : Space n,a≠0 → ‖a‖≤δ →
          Integrable (fun x => η x^2*((((j:ℝ)+1)⁻¹)^2+
            (max ‖(gf+gw j) (x+a)‖ ‖(gf+gw j) x‖)^2)^((p-2)/2)*
            ‖‖a‖⁻¹ • ((gf+gw j) (x+a)-(gf+gw j) x)‖^2)
            (volume.restrict (Ω∩((fun x => x+a) ⁻¹' Ω))) ∧
          (∫ x in Ω∩((fun x => x+a) ⁻¹' Ω),η x^2*
            ((((j:ℝ)+1)⁻¹)^2+(max ‖(gf+gw j) (x+a)‖ ‖(gf+gw j) x‖)^2)^((p-2)/2)*
            ‖‖a‖⁻¹ • ((gf+gw j) (x+a)-(gf+gw j) x)‖^2)≤M) ∧
      Tendsto (fun j=>eLpNorm (gw j) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) ∧
      Tendsto (fun j=>eLpNorm (w j) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) := by
  obtain ⟨w,gw,hw,hu,hrows,hg,hwlim⟩ :=
    hH.exists_regularized_source_W1p_approximants_with_weak_hessian hf hp hn hΩb
  have hp1 : 1≤ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hf.1.le
  obtain ⟨U,hU,hUbound⟩ := hessian_uniform_norm_of_strong_corrections hp1 hf.2.1
    (fun j => (hw j).1.2.1) hwlim
  obtain ⟨N,hN,hNbound⟩ := hessian_uniform_norm_of_strong_corrections hp1 hf.2.2.1
    (fun j => (hw j).1.2.2.1) hg
  refine ⟨w,gw,hw,hu,hrows,?_,hg,hwlim⟩
  intro η hη hη0
  have hεN (j : ℕ) : ((j:ℝ)+1)⁻¹≠0 := inv_ne_zero (by positivity : (j:ℝ)+1≠0)
  have hεb (j : ℕ) : |((j:ℝ)+1)⁻¹|≤1 := by
    rw [abs_of_pos (inv_pos.mpr (by positivity : 0<(j:ℝ)+1))]
    exact inv_le_one_of_one_le₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) j])
  exact exists_uniform_weighted_gradient_quotient_bound_of_uniform_sobolev_data hu hp hεN hεb
    hΩb hU hN hUbound hNbound hη hη0

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.exists_regularized_source_approximants_uniform_weighted_quotients
