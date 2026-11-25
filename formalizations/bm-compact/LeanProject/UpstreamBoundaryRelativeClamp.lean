import ExteriorCapacityClamp

/-! Actual unit bounds for bounded relative capacity in the genuine W0 graph.
Private smooth-clamp mechanisms are adapted from the previously authored checked
ExteriorCapacityClamp; no new proof count is assigned to those helper bodies.
All pointwise smooth obstacle constraints and both actual Lp limits are retained. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal ContDiff
namespace BMCompactPDE

private theorem exterior_positivePart_nonneg (j : ℕ) (t : ℝ) :
    0 ≤ smoothPositivePart j t := by
  by_cases ht : t ≤ 0
  · rw [smoothPositivePart_eq_zero_of_nonpos j ht]
  · exact mul_nonneg (lt_of_not_ge ht).le (Real.smoothTransition.nonneg _)

private theorem exterior_positivePart_le_max (j : ℕ) (t : ℝ) :
    smoothPositivePart j t ≤ max t 0 := by
  by_cases ht : t ≤ 0
  · rw [smoothPositivePart_eq_zero_of_nonpos j ht, max_eq_right ht]
  · rw [max_eq_left (lt_of_not_ge ht).le]
    exact (mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) (lt_of_not_ge ht).le).trans_eq (mul_one _)

private theorem exterior_shift_positivePart_norm_le (j : ℕ) (t : ℝ) :
    ‖smoothPositivePart j (t-1)‖ ≤ ‖t‖ := by
  by_cases ht : t ≤ 1
  · rw [smoothPositivePart_eq_zero_of_nonpos j (by linarith)]
    simpa only [norm_zero] using norm_nonneg t
  · have hp : 0 ≤ t := by linarith
    have hs : 0 ≤ t-1 := by linarith
    calc
      ‖smoothPositivePart j (t-1)‖ ≤ ‖t-1‖ := smoothPositivePart_norm_le j _
      _ = t-1 := by rw [Real.norm_eq_abs, abs_of_nonneg hs]
      _ ≤ ‖t‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hp]; linarith

private theorem exteriorSmoothUnitClamp_contDiff (j : ℕ) :
    ContDiff ℝ ∞ (exteriorSmoothUnitClamp j) :=
  (smoothPositivePart_contDiff j).sub
    ((smoothPositivePart_contDiff j).comp (contDiff_id.sub contDiff_const))

private theorem exteriorSmoothUnitClamp_hasDerivAt (j : ℕ) (t : ℝ) :
    HasDerivAt (exteriorSmoothUnitClamp j) (exteriorSmoothUnitClampSlope j t) t := by
  have hs := (smoothPositivePart_hasDerivAt j (t-1)).comp t ((hasDerivAt_id t).sub_const 1)
  convert! (smoothPositivePart_hasDerivAt j t).sub hs using 1 <;>
    simp only [exteriorSmoothUnitClamp, exteriorSmoothUnitClampSlope, Pi.sub_apply,
      Function.comp_apply, id_eq, mul_one, sub_zero]

private theorem exteriorSmoothUnitClamp_zero (j : ℕ) : exteriorSmoothUnitClamp j 0 = 0 := by
  simp only [exteriorSmoothUnitClamp, smoothPositivePart_eq_zero_of_nonpos j (le_refl (0 : ℝ)),
    smoothPositivePart_eq_zero_of_nonpos j (by norm_num : (0 : ℝ)-1 ≤ 0), sub_self]

private theorem exteriorSmoothUnitClamp_one_le (j : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    1 ≤ exteriorSmoothUnitClamp j t := by
  have hj : (1 : ℝ) ≤ (j : ℝ)+1 := by
    have hzero : (0 : ℝ) ≤ (j : ℝ) := by positivity
    linarith
  have hs : 1 ≤ ((j : ℝ)+1)*t := by
    exact (one_le_mul_of_one_le_of_one_le hj ht)
  rw [exteriorSmoothUnitClamp, smoothPositivePart_eq_self_of_one_le j hs]
  have hh := exterior_positivePart_le_max j (t-1)
  rw [max_eq_left (sub_nonneg.mpr ht)] at hh
  linarith

private theorem exteriorSmoothUnitClamp_norm_le (j : ℕ) (t : ℝ) :
    ‖exteriorSmoothUnitClamp j t‖ ≤ 2*‖t‖ := by
  exact (norm_sub_le _ _).trans ((add_le_add (smoothPositivePart_norm_le j t)
    (exterior_shift_positivePart_norm_le j t)).trans_eq (by ring))

private theorem exteriorSmoothUnitClampSlope_continuous (j : ℕ) :
    Continuous (exteriorSmoothUnitClampSlope j) :=
  (continuous_positivePartSlope j).sub
    ((continuous_positivePartSlope j).comp (continuous_id.sub continuous_const))

private theorem exteriorSmoothUnitClampSlope_bound {C : ℝ}
    (hC : ∀ j t, ‖positivePartSlope j t‖ ≤ C) (j : ℕ) (t : ℝ) :
    ‖exteriorSmoothUnitClampSlope j t‖ ≤ 2*C :=
  (norm_sub_le _ _).trans ((add_le_add (hC j t) (hC j (t-1))).trans_eq (by ring))

private theorem exteriorSmoothUnitClamp_norm_sub_le (j : ℕ) {C : ℝ}
    (hC : ∀ j t, ‖positivePartSlope j t‖ ≤ C) (a b : ℝ) :
    ‖exteriorSmoothUnitClamp j a-exteriorSmoothUnitClamp j b‖ ≤ (2*C)*‖a-b‖ := by
  apply convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (exteriorSmoothUnitClamp_hasDerivAt j t).differentiableAt)
    (fun t _ => ?_) (mem_univ b) (mem_univ a)
  rw [(exteriorSmoothUnitClamp_hasDerivAt j t).deriv]
  exact exteriorSmoothUnitClampSlope_bound hC j t

private theorem exteriorUnitClamp_bounds (t : ℝ) :
    0 ≤ exteriorUnitClamp t ∧ exteriorUnitClamp t ≤ 1 ∧ ‖exteriorUnitClamp t‖ ≤ ‖t‖ := by
  by_cases h0 : t ≤ 0
  · have h1 : t-1 ≤ 0 := by linarith
    simp only [exteriorUnitClamp, max_eq_right h0, max_eq_right h1, sub_self, norm_zero]
    exact ⟨le_rfl, zero_le_one, norm_nonneg _⟩
  · have hp : 0<t := lt_of_not_ge h0
    by_cases h1 : t ≤ 1
    · simp only [exteriorUnitClamp, max_eq_left hp.le, max_eq_right (by linarith : t-1 ≤ 0), sub_zero]
      exact ⟨hp.le, h1, le_rfl⟩
    · have hs : 0≤t-1 := by linarith
      have he : exteriorUnitClamp t=1 := by
        rw [exteriorUnitClamp, max_eq_left hp.le, max_eq_left hs]
        ring
      rw [he]
      refine ⟨zero_le_one, le_rfl, ?_⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ)≤1), Real.norm_eq_abs, abs_of_nonneg hp.le]
      linarith

private theorem exteriorUnitClampSlope_bound (t : ℝ) : ‖exteriorUnitClampSlope t‖ ≤ 1 := by
  by_cases h0 : 0<t
  · by_cases h1 : 0<t-1 <;> simp [exteriorUnitClampSlope, h0, h1]
  · have h1 : ¬0<t-1 := by linarith
    simp only [exteriorUnitClampSlope, if_neg h0, if_neg h1, sub_self, norm_zero, zero_le_one]

private theorem exteriorSmoothUnitClamp_eventually (t : ℝ) :
    ∀ᶠ j : ℕ in atTop, exteriorSmoothUnitClamp j t = exteriorUnitClamp t := by
  filter_upwards [smoothPositivePart_eventually_eq t, smoothPositivePart_eventually_eq (t-1)] with j h0 h1
  simp only [exteriorSmoothUnitClamp, exteriorUnitClamp, h0, h1]

private theorem exteriorSmoothUnitClampSlope_eventually (t : ℝ) :
    ∀ᶠ j : ℕ in atTop, exteriorSmoothUnitClampSlope j t = exteriorUnitClampSlope t := by
  filter_upwards [positivePartSlope_eventually_eq t, positivePartSlope_eventually_eq (t-1)] with j h0 h1
  simp only [exteriorSmoothUnitClampSlope, exteriorUnitClampSlope, h0, h1]

private theorem gradient_exteriorSmoothUnitClamp {n : ℕ} {φ : Space n → ℝ}
    (hφ : Differentiable ℝ φ) (j : ℕ) (x : Space n) :
    gradient (fun y => exteriorSmoothUnitClamp j (φ y)) x =
      exteriorSmoothUnitClampSlope j (φ x) • gradient φ x := by
  have hd := (exteriorSmoothUnitClamp_hasDerivAt j (φ x)).comp_hasFDerivAt x (hφ x).hasFDerivAt
  unfold gradient
  change (InnerProductSpace.toDual ℝ (Space n)).symm
    (fderiv ℝ (exteriorSmoothUnitClamp j ∘ φ) x) = _
  rw [hd.fderiv]
  exact map_smul (InnerProductSpace.toDual ℝ (Space n)).symm _ _


variable (p : ℝ) [Fact (1≤ENNReal.ofReal p)]

private theorem upstream_relative_class_of_member_limits (hp : 1<p) {n : ℕ} {K O : Set (Space n)}
    {w : ℕ → w0LpGraph p hp n O} (hw : ∀ j,w j∈exteriorRelativeCapacityClass p hp K O)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : MemLp u (ENNReal.ofReal p) (volume.restrict O))
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict O))
    (hlu : Tendsto (fun j=>eLpNorm (((w j).1.1 : Space n → ℝ)-u) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0))
    (hlg : Tendsto (fun j=>eLpNorm (((w j).1.2 : Space n → Space n)-g) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0)) :
    ∃ z∈exteriorRelativeCapacityClass p hp K O,
      (z.1.1 : Space n → ℝ)=ᵐ[volume.restrict O] u ∧ (z.1.2 : Space n → Space n)=ᵐ[volume.restrict O] g := by
  let z0 : ScalarLp p n O × VectorLp p n O := (hu.toLp u,hg.toLp g)
  have h1 : Tendsto (fun j=>(w j).1.1) atTop (𝓝 z0.1) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j=>(w j).1.1) (hu.toLp u)).mpr
    have he (j : ℕ) : eLpNorm (((w j).1.1 : Space n → ℝ)-(hu.toLp u : Space n → ℝ))
        (ENNReal.ofReal p) (volume.restrict O)=eLpNorm (((w j).1.1 : Space n → ℝ)-u) (ENNReal.ofReal p) (volume.restrict O) :=
      eLpNorm_congr_ae (EventuallyEq.rfl.sub hu.coeFn_toLp)
    simpa only [he] using hlu
  have h2 : Tendsto (fun j=>(w j).1.2) atTop (𝓝 z0.2) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j=>(w j).1.2) (hg.toLp g)).mpr
    have he (j : ℕ) : eLpNorm (((w j).1.2 : Space n → Space n)-(hg.toLp g : Space n → Space n))
        (ENNReal.ofReal p) (volume.restrict O)=eLpNorm (((w j).1.2 : Space n → Space n)-g) (ENNReal.ofReal p) (volume.restrict O) :=
      eLpNorm_congr_ae (EventuallyEq.rfl.sub hg.coeFn_toLp)
    simpa only [he] using hlg
  have hprod : Tendsto (fun j=>(w j).1) atTop (𝓝 z0) := h1.prodMk_nhds h2
  have hz0 : z0∈w0LpGraph p hp n O :=
    (isClosed_w0LpGraph p hp n O).mem_of_tendsto hprod (Eventually.of_forall (fun j=>(w j).2))
  let z : w0LpGraph p hp n O := ⟨z0,hz0⟩
  have hsub : Tendsto w atTop (𝓝 z) := tendsto_subtype_rng.mpr hprod
  exact ⟨z,isClosed_closure.mem_of_tendsto hsub (Eventually.of_forall hw),hu.coeFn_toLp,hg.coeFn_toLp⟩

private theorem upstream_relative_class_of_admissible_limits (hp : 1<p) {n : ℕ} {K O : Set (Space n)}
    {φ : ℕ → Space n → ℝ} (hφ : ∀ j,BMCompactCapacityV2.Admissible K O (φ j))
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : MemLp u (ENNReal.ofReal p) (volume.restrict O))
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict O))
    (hlu : Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0))
    (hlg : Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0)) :
    ∃ z∈exteriorRelativeCapacityClass p hp K O,
      (z.1.1 : Space n → ℝ)=ᵐ[volume.restrict O] u ∧ (z.1.2 : Space n → Space n)=ᵐ[volume.restrict O] g := by
  have hex (j : ℕ) : ∃ w : w0LpGraph p hp n O,w∈exteriorRelativeCapacitySmoothClass p hp K O ∧
      (w.1.1 : Space n → ℝ)=ᵐ[volume.restrict O] φ j ∧
      (w.1.2 : Space n → Space n)=ᵐ[volume.restrict O] gradient (φ j) := by
    have ht : SmoothTest O (φ j) := ⟨(hφ j).1,(hφ j).2.1,(hφ j).2.2.1⟩
    obtain ⟨w,hwu,hwg⟩ := (ht.zeroBoundarySobolevPair hp).exists_w0LpGraph_representatives hp
    exact ⟨w,⟨φ j,hφ j,hwu,hwg⟩,hwu,hwg⟩
  choose w hw hwu hwg using hex
  apply upstream_relative_class_of_member_limits p hp (fun j=>subset_closure (hw j)) hu hg
  · have he (j : ℕ) : eLpNorm (((w j).1.1 : Space n → ℝ)-u) (ENNReal.ofReal p) (volume.restrict O)=
        eLpNorm (φ j-u) (ENNReal.ofReal p) (volume.restrict O) := eLpNorm_congr_ae ((hwu j).sub EventuallyEq.rfl)
    simpa only [he] using hlu
  · have he (j : ℕ) : eLpNorm (((w j).1.2 : Space n → Space n)-g) (ENNReal.ofReal p) (volume.restrict O)=
        eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) (volume.restrict O) :=
      eLpNorm_congr_ae ((hwg j).sub EventuallyEq.rfl)
    simpa only [he] using hlg

private theorem upstream_relative_class_smooth_clamp {n : ℕ} (hp : 1<p)
    {K O : Set (Space n)} {w : w0LpGraph p hp n O}
    (hw : w ∈ exteriorRelativeCapacityClass p hp K O) (k : ℕ) :
    ∃ z ∈ exteriorRelativeCapacityClass p hp K O,
      (z.1.1 : Space n → ℝ) =ᵐ[(volume.restrict O)] (fun x => exteriorSmoothUnitClamp k (w.1.1 x)) ∧
      (z.1.2 : Space n → Space n) =ᵐ[(volume.restrict O)]
        (fun x => exteriorSmoothUnitClampSlope k (w.1.1 x) • w.1.2 x) := by
  let u : Space n → ℝ := w.1.1
  let g : Space n → Space n := w.1.2
  have hu : MemLp u (ENNReal.ofReal p) (volume.restrict O) := Lp.memLp w.1.1
  have hg : MemLp g (ENNReal.ofReal p) (volume.restrict O) := Lp.memLp w.1.2
  obtain ⟨φ, hφ, hLu, hLg⟩ := exteriorRelativeCapacityClass_smooth_approximation p hp hw
  have hφu (j : ℕ) : MemLp (φ j) (ENNReal.ofReal p) (volume.restrict O) :=
    (BMCompactCapacityV2.smooth_compactSupport_memLp (ENNReal.ofReal p) (hφ j).1 (hφ j).2.1).restrict O
  have hφg (j : ℕ) : MemLp (gradient (φ j)) (ENNReal.ofReal p) (volume.restrict O) :=
    (BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p) (hφ j).1 (hφ j).2.1).restrict O
  have hq0 := ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp)
  have hm := tendstoInMeasure_of_tendsto_eLpNorm hq0 (fun j => (hφu j).1) hu.1 hLu
  obtain ⟨σ, hσ, hσlim⟩ := hm.exists_seq_tendsto_ae
  obtain ⟨C, hC, hbound⟩ := positivePartSlope_uniform_bound
  have hC0 : 0≤C := zero_le_one.trans hC
  have hC2 : 0≤2*C := by positivity
  let ψ : ℕ → Space n → ℝ := fun j x => exteriorSmoothUnitClamp k (φ (σ j) x)
  have hψ (j : ℕ) : BMCompactCapacityV2.Admissible K O (ψ j) :=
    exteriorSmoothUnitClamp_preserves_admissible (hφ (σ j)) k
  have hFu : MemLp (fun x => exteriorSmoothUnitClamp k (u x)) (ENNReal.ofReal p) (volume.restrict O) := by
    apply (hu.const_smul (2 : ℝ)).of_le
      ((exteriorSmoothUnitClamp_contDiff k).continuous.comp_aestronglyMeasurable hu.1)
    exact Eventually.of_forall (fun x => by
      simpa only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
        using exteriorSmoothUnitClamp_norm_le k (u x))
  have hDmeas : AEStronglyMeasurable (fun x => exteriorSmoothUnitClampSlope k (u x)) (volume.restrict O) :=
    (exteriorSmoothUnitClampSlope_continuous k).comp_aestronglyMeasurable hu.1
  have hDg : MemLp (fun x => exteriorSmoothUnitClampSlope k (u x) • g x)
      (ENNReal.ofReal p) (volume.restrict O) := by
    apply (hg.const_smul (2*C)).of_le (hDmeas.smul hg.1)
    exact Eventually.of_forall (fun x => by
      simp only [Pi.smul_apply, Pi.smul_apply', norm_smul, Real.norm_eq_abs, abs_of_nonneg hC2]
      exact mul_le_mul_of_nonneg_right (exteriorSmoothUnitClampSlope_bound hbound k (u x)) (norm_nonneg (g x)))
  apply upstream_relative_class_of_admissible_limits p hp hψ hFu hDg
  · have hb (j : ℕ) : eLpNorm (ψ j-(fun x => exteriorSmoothUnitClamp k (u x)))
        (ENNReal.ofReal p) (volume.restrict O) ≤ ‖2*C‖ₑ*eLpNorm (φ (σ j)-u) (ENNReal.ofReal p) (volume.restrict O) := by
      rw [←eLpNorm_const_smul]
      apply eLpNorm_mono
      intro x
      simpa only [ψ, Pi.sub_apply, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hC2]
        using exteriorSmoothUnitClamp_norm_sub_le k hbound (φ (σ j) x) (u x)
    have ht := ENNReal.Tendsto.const_mul (a := ‖2*C‖ₑ)
      (hLu.comp hσ.tendsto_atTop) (Or.inr enorm_ne_top)
    rw [mul_zero] at ht
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) hb
  · have hgradient (j : ℕ) : gradient (ψ j) =
        fun x => exteriorSmoothUnitClampSlope k (φ (σ j) x) • gradient (φ (σ j)) x := by
      funext x
      exact gradient_exteriorSmoothUnitClamp ((hφ (σ j)).1.differentiable (by simp)) k x
    simp_rw [hgradient]
    apply tendsto_eLpNorm_bounded_smul
      (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp)) ENNReal.ofReal_ne_top
      (ENNReal.one_le_ofReal.mpr hp.le) hC2
      (fun j => (exteriorSmoothUnitClampSlope_continuous k).comp_aestronglyMeasurable (hφu (σ j)).1)
      hDmeas (fun j => hφg (σ j)) hg
      (fun j x => exteriorSmoothUnitClampSlope_bound hbound k (φ (σ j) x))
      (fun x => exteriorSmoothUnitClampSlope_bound hbound k (u x))
    · filter_upwards [hσlim] with x hx
      exact (exteriorSmoothUnitClampSlope_continuous k).continuousAt.tendsto.comp hx
    · exact hLg.comp hσ.tendsto_atTop

set_option maxHeartbeats 1500000 in
private theorem upstream_relative_class_clamp {n : ℕ} (hp : 1<p)
    {K O : Set (Space n)} {w : w0LpGraph p hp n O}
    (hw : w ∈ exteriorRelativeCapacityClass p hp K O) :
    ∃ z ∈ exteriorRelativeCapacityClass p hp K O,
      (z.1.1 : Space n → ℝ) =ᵐ[(volume.restrict O)] (fun x => exteriorUnitClamp (w.1.1 x)) ∧
      (z.1.2 : Space n → Space n) =ᵐ[(volume.restrict O)]
        (fun x => exteriorUnitClampSlope (w.1.1 x) • w.1.2 x) ∧ ‖z.1.2‖ ≤ ‖w.1.2‖ := by
  let u : Space n → ℝ := w.1.1
  let g : Space n → Space n := w.1.2
  have hu : MemLp u (ENNReal.ofReal p) (volume.restrict O) := Lp.memLp w.1.1
  have hg : MemLp g (ENNReal.ofReal p) (volume.restrict O) := Lp.memLp w.1.2
  have hUcont : Continuous exteriorUnitClamp :=
    (continuous_id.max continuous_const).sub
      ((continuous_id.sub continuous_const).max continuous_const)
  have hUmeas : AEStronglyMeasurable (fun x => exteriorUnitClamp (u x)) (volume.restrict O) :=
    hUcont.comp_aestronglyMeasurable hu.1
  have hUmem : MemLp (fun x => exteriorUnitClamp (u x)) (ENNReal.ofReal p) (volume.restrict O) :=
    hu.of_le hUmeas (Eventually.of_forall (fun x => (exteriorUnitClamp_bounds (u x)).2.2))
  have hDlim : ∀ᵐ x ∂(volume.restrict O), Tendsto (fun j => exteriorSmoothUnitClampSlope j (u x))
      atTop (𝓝 (exteriorUnitClampSlope (u x))) :=
    Eventually.of_forall (fun x => tendsto_const_nhds.congr'
      ((exteriorSmoothUnitClampSlope_eventually (u x)).mono (fun j hj => hj.symm)))
  have hDmeas : AEStronglyMeasurable (fun x => exteriorUnitClampSlope (u x)) (volume.restrict O) :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun j => (exteriorSmoothUnitClampSlope_continuous j).comp_aestronglyMeasurable hu.1) hDlim
  have hGmeas : AEStronglyMeasurable (fun x => exteriorUnitClampSlope (u x) • g x) (volume.restrict O) :=
    hDmeas.smul hg.1
  have hGnorm (x : Space n) : ‖exteriorUnitClampSlope (u x) • g x‖ ≤ ‖g x‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (exteriorUnitClampSlope_bound (u x)) (norm_nonneg _)).trans_eq (one_mul _)
  have hGmem : MemLp (fun x => exteriorUnitClampSlope (u x) • g x) (ENNReal.ofReal p) (volume.restrict O) :=
    hg.of_le hGmeas (Eventually.of_forall hGnorm)
  have hlu : Tendsto (fun j => eLpNorm
      ((fun x => exteriorSmoothUnitClamp j (u x))-(fun x => exteriorUnitClamp (u x)))
      (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_zero_of_dominated
      (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp)) ENNReal.ofReal_ne_top
      (b := (3 : ℝ) • u)
    · intro j
      exact ((exteriorSmoothUnitClamp_contDiff j).continuous.comp_aestronglyMeasurable hu.1).sub hUmeas
    · exact hu.const_smul (3 : ℝ)
    · intro j
      exact Eventually.of_forall (fun x => by
        calc
          ‖exteriorSmoothUnitClamp j (u x)-exteriorUnitClamp (u x)‖ ≤
              ‖exteriorSmoothUnitClamp j (u x)‖+‖exteriorUnitClamp (u x)‖ := norm_sub_le _ _
          _ ≤ 2*‖u x‖+‖u x‖ := add_le_add (exteriorSmoothUnitClamp_norm_le j _) (exteriorUnitClamp_bounds _).2.2
          _ = ‖((3 : ℝ) • u) x‖ := by simp only [Pi.smul_apply, norm_smul]; norm_num; ring)
    · exact Eventually.of_forall (fun x => tendsto_const_nhds.congr'
        ((exteriorSmoothUnitClamp_eventually (u x)).mono (fun j hj => by simp only [Pi.sub_apply, hj, sub_self])))
  obtain ⟨C, hC, hbound⟩ := positivePartSlope_uniform_bound
  have hC0 : 0≤C := zero_le_one.trans hC
  have hlg : Tendsto (fun j => eLpNorm
      ((fun x => exteriorSmoothUnitClampSlope j (u x) • g x)-
        (fun x => exteriorUnitClampSlope (u x) • g x))
      (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_zero_of_dominated
      (ENNReal.ofReal_ne_zero_iff.mpr (zero_lt_one.trans hp)) ENNReal.ofReal_ne_top
      (b := (2*C+1) • g)
    · intro j
      exact (((exteriorSmoothUnitClampSlope_continuous j).comp_aestronglyMeasurable hu.1).smul hg.1).sub hGmeas
    · exact hg.const_smul (2*C+1)
    · intro j
      exact Eventually.of_forall (fun x => by
        calc
          ‖exteriorSmoothUnitClampSlope j (u x) • g x-exteriorUnitClampSlope (u x) • g x‖ ≤
              ‖exteriorSmoothUnitClampSlope j (u x) • g x‖+‖exteriorUnitClampSlope (u x) • g x‖ := norm_sub_le _ _
          _ ≤ (2*C)*‖g x‖+‖g x‖ := by
            rw [norm_smul]
            exact add_le_add (mul_le_mul_of_nonneg_right (exteriorSmoothUnitClampSlope_bound hbound j _) (norm_nonneg _)) (hGnorm x)
          _ = ‖((2*C+1) • g) x‖ := by
            simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0≤2*C+1)]
            ring)
    · exact Eventually.of_forall (fun x => tendsto_const_nhds.congr'
        ((exteriorSmoothUnitClampSlope_eventually (u x)).mono (fun j hj => by simp only [Pi.sub_apply, hj, sub_self])))
  choose z hz hzu hzg using (fun j => upstream_relative_class_smooth_clamp p hp hw j)
  have hzulim : Tendsto (fun j => eLpNorm (((z j).1.1 : Space n → ℝ)-(fun x => exteriorUnitClamp (u x)))
      (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) := by
    have he (j : ℕ) : eLpNorm (((z j).1.1 : Space n → ℝ)-(fun x => exteriorUnitClamp (u x))) (ENNReal.ofReal p) (volume.restrict O) =
        eLpNorm ((fun x => exteriorSmoothUnitClamp j (u x))-(fun x => exteriorUnitClamp (u x)))
          (ENNReal.ofReal p) (volume.restrict O) := eLpNorm_congr_ae ((hzu j).sub EventuallyEq.rfl)
    simpa only [he] using hlu
  have hzglim : Tendsto (fun j => eLpNorm (((z j).1.2 : Space n → Space n)-(fun x => exteriorUnitClampSlope (u x) • g x))
      (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) := by
    have he (j : ℕ) : eLpNorm (((z j).1.2 : Space n → Space n)-(fun x => exteriorUnitClampSlope (u x) • g x)) (ENNReal.ofReal p) (volume.restrict O) =
        eLpNorm ((fun x => exteriorSmoothUnitClampSlope j (u x) • g x)-
          (fun x => exteriorUnitClampSlope (u x) • g x)) (ENNReal.ofReal p) (volume.restrict O) :=
      eLpNorm_congr_ae ((hzg j).sub EventuallyEq.rfl)
    simpa only [he] using hlg
  obtain ⟨v, hv, hvu, hvg⟩ := upstream_relative_class_of_member_limits p hp hz hUmem hGmem hzulim hzglim
  refine ⟨v, hv, hvu, hvg, ?_⟩
  have he : eLpNorm (v.1.2 : Space n → Space n) (ENNReal.ofReal p) (volume.restrict O) ≤
      eLpNorm (w.1.2 : Space n → Space n) (ENNReal.ofReal p) (volume.restrict O) := by
    rw [eLpNorm_congr_ae hvg]
    exact eLpNorm_mono hGnorm
  simpa only [Lp.norm_def] using ENNReal.toReal_mono (Lp.eLpNorm_ne_top w.1.2) he

/-- Actual unit-bounded relative capacitary potential, for every p>1 and
arbitrary compact K inside bounded open O. The clamp is a genuine member of
the original strong smooth-admissible W0 closure and contracts gradient energy.
No unit bound, minimum, approximation, solution or trace is an input. -/
theorem exists_bounded_relative_capacity_potential_unit_bounds_allp {n : ℕ} {p : ℝ}
    (hp : 1<p) (hn : 2≤n) {K O : Set (Space n)} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K⊆O) (hOb : Bornology.IsBounded O) :
    ∃ u : Space n → ℝ,∃ g : Space n → Space n,
      ZeroBoundarySobolevPair p O u g ∧ WeakPHarmonicPair p (O\K) u g ∧
      (∀ᵐ x ∂volume.restrict O,0≤u x ∧ u x≤1) ∧
      BMCompactCapacityV2.relativeCapacity p K O=ENNReal.ofReal (∫ x in O,‖g x‖^p ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K O (φ j)) ∧
        Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) ∧
        Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨w,hw,hm⟩ := exists_exteriorRelativeCapacityClass_minimum p hp hn hK hO hKO hOb
  obtain ⟨z,hz,hzu,-,hnorm⟩ := upstream_relative_class_clamp p hp hw
  have hmin : ∀ v∈exteriorRelativeCapacityClass p hp K O,‖z.1.2‖^p≤‖v.1.2‖^p := by
    intro v hv
    exact (Real.rpow_le_rpow (norm_nonneg _) hnorm (zero_lt_one.trans hp).le).trans (hm v hv)
  have hunit : ∀ᵐ x ∂volume.restrict O,0≤(z.1.1 : Space n → ℝ) x ∧ (z.1.1 : Space n → ℝ) x≤1 := by
    filter_upwards [hzu] with x hx
    rw [hx]
    exact ⟨(exteriorUnitClamp_bounds (w.1.1 x)).1,(exteriorUnitClamp_bounds (w.1.1 x)).2.1⟩
  have he := relativeCapacity_eq_exteriorRelativeCapacityClass_minimum_energy p hp hz hmin
  rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)] at he
  exact ⟨(z.1.1 : Space n → ℝ),(z.1.2 : Space n → Space n),z.2,
    exteriorRelativeCapacityClass_minimum_weakPHarmonic p hp hK.isClosed hO z hz hmin,hunit,he,
    exteriorRelativeCapacityClass_smooth_approximation p hp hz⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_bounded_relative_capacity_potential_unit_bounds_allp
