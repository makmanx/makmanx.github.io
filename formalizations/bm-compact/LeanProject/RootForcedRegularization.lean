import GradientRegularizedDifference

/-! Strong actual W1,p convergence of regularized constant-source Dirichlet
solutions, including nonzero forcing. The only approximation parameter input is scalar epsilon tending
to zero. The final theorem constructs the actual solution family itself.
No selected classical representative or classical regularity is inferred. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal
namespace BMCompactPDE

private theorem root_forced_energy_eq_lp_power
    {n : ℕ} {p : ℝ} (hp : 1<p) {μ : Measure (Space n)}
    {g : Space n → Space n} (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫ x,‖g x‖^p ∂μ)=‖hg.toLp g‖^p := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have he := integral_congr_ae ((MemLp.coeFn_toLp hg).fun_comp (fun v=>‖v‖^p))
  exact he.symm.trans (BMCompactNonlinear.lp_norm_rpow_eq_integral
    (zero_lt_one.trans hp) (hg.toLp g)).symm

private theorem root_forced_lp_midpoint_minimum
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {f w : Space n → ℝ} {gf gw : Space n → Space n}
    (hH : WeakPSourcePair p c Ω f gf) (hf : SobolevPair p Ω f gf)
    (hw : ZeroBoundarySobolevPair p Ω w gw) (hΩb : Bornology.IsBounded Ω) :
    ‖hf.2.2.1.toLp gf‖^p+p*c*((1/2 : ℝ)*(∫ x in Ω,w x)) ≤
      ‖(1/2 : ℝ) • ((hf.2.2.1.toLp gf+hw.1.2.2.1.toLp gw)+hf.2.2.1.toLp gf)‖^p := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hf.1.le⟩
  have hm := hH.energy_tangent_global hΩb hf (hw.smul_actual (1/2 : ℝ))
  rw [show (fun x => ((1/2 : ℝ) • w) x)=(fun x => (1/2 : ℝ)*w x) by rfl, integral_const_mul] at hm
  change (∫ x in Ω,‖gf x‖^p)+p*c*((1/2 : ℝ)*(∫ x in Ω,w x))≤∫ x in Ω,‖(gf+(1/2 : ℝ) • gw) x‖^p at hm
  rw [root_forced_energy_eq_lp_power hf.1 hf.2.2.1,
    root_forced_energy_eq_lp_power hf.1 (hf.2.2.1.add (hw.1.2.2.1.const_smul (1/2 : ℝ))),
    MemLp.toLp_add hf.2.2.1 (hw.1.2.2.1.const_smul (1/2 : ℝ)),
    MemLp.toLp_const_smul (1/2 : ℝ) hw.1.2.2.1] at hm
  have hvec : hf.2.2.1.toLp gf+(1/2 : ℝ) • hw.1.2.2.1.toLp gw=
      (1/2 : ℝ) • ((hf.2.2.1.toLp gf+hw.1.2.2.1.toLp gw)+hf.2.2.1.toLp gf) := by module
  simpa only [hvec] using hm

private theorem root_forced_physical_energy_le_augmented
    {n : ℕ} {p ε : ℝ} (hp : 1<p) {μ : Measure (Space n)} [IsFiniteMeasure μ]
    {g : Space n → Space n} (hg : MemLp g (ENNReal.ofReal p) μ) :
    (∫ x,‖g x‖^p ∂μ)≤∫ x,‖(WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)‖^p ∂μ := by
  have hG : MemLp (fun x => (WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n))
      (ENNReal.ofReal p) μ := by
    have hh := (memLp_const (WithLp.toLp 2 (ε,(0 : Space n)) : GradientAugmentedSpace n)).add
      (hg.continuousLinearMap_comp (gradientAugmentedInjection n))
    convert! hh using 1
    funext x
    simp only [Pi.add_apply]
    rw [gradientAugmentedInjection_apply,←WithLp.toLp_add]
    congr 1
    ext <;> simp
  have hp0 : 0<p := zero_lt_one.trans hp
  have hGI : Integrable (fun x => ‖(WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)‖^p) μ := by
    simpa only [ENNReal.toReal_ofReal hp0.le] using
      hG.integrable_norm_rpow (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  exact integral_mono (integrable_norm_rpow_of_memLp hp hg) hGI
    (fun x => Real.rpow_le_rpow (norm_nonneg _)
      (WithLp.norm_snd_le ℝ (WithLp.toLp 2 (ε,g x) : GradientAugmentedSpace n)) hp0.le)

set_option maxHeartbeats 1600000 in
theorem WeakPSourcePair.regularized_source_family_W1p_tendsto
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hH : WeakPSourcePair p c Ω f gf) (hf : SobolevPair p Ω f gf)
    (hn : 2≤n) (hΩb : Bornology.IsBounded Ω)
    {ε : ℕ → ℝ} {w : ℕ → Space n → ℝ} {gw : ℕ → Space n → Space n}
    (hw : ∀ j,ZeroBoundarySobolevPair p Ω (w j) (gw j))
    (hu : ∀ j,GlobalWeakRegularizedSourcePair p (ε j) c Ω (f+w j) (gf+gw j))
    (hεb : ∀ j,|ε j|≤1) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j=>eLpNorm (gw j) (ENNReal.ofReal p) (volume.restrict Ω))
      atTop (𝓝 0) ∧
    Tendsto (fun j=>eLpNorm (w j) (ENNReal.ofReal p) (volume.restrict Ω))
      atTop (𝓝 0) := by
  letI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hf.1.le⟩
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  have hp0 : 0<p := zero_lt_one.trans hf.1
  let μ := volume.restrict Ω
  let T := gradientAugmentedLpInjection p Ω
  let F := hf.2.2.1.toLp gf
  let G (j : ℕ) := (hw j).1.2.2.1.toLp (gw j)
  let A (j : ℕ) := F+G j
  let C0 : GradientAugmentedSpace n := WithLp.toLp 2 ((1 : ℝ),(0 : Space n))
  have hC : MemLp (fun _ : Space n => C0) (ENNReal.ofReal p) μ := memLp_const C0
  let C := hC.toLp (fun _ : Space n => C0)
  let B (j : ℕ) := ε j • C+T F
  have hTF : T F=ᵐ[μ] fun x => gradientAugmentedInjection n (gf x) := by
    filter_upwards [(gradientAugmentedInjection n).coeFn_compLpL F,hf.2.2.1.coeFn_toLp]
      with x hx hFx
    change ((gradientAugmentedInjection n).compLpL (ENNReal.ofReal p) (volume.restrict Ω) F) x=_
    change F x=gf x at hFx
    rw [hx,hFx]
  have hBae (j : ℕ) : B j=ᵐ[μ] fun x => (WithLp.toLp 2 (ε j,gf x) : GradientAugmentedSpace n) := by
    filter_upwards [Lp.coeFn_add (ε j • C) (T F),Lp.coeFn_smul (ε j) C,hC.coeFn_toLp,hTF]
      with x hadd hsm hCx hTx
    change ((ε j • C+T F) : Lp (GradientAugmentedSpace n) (ENNReal.ofReal p) μ) x=_
    rw [hadd,Pi.add_apply,hsm,Pi.smul_apply,hCx,hTx]
    change ε j • (WithLp.toLp 2 ((1 : ℝ),(0 : Space n)))+gradientAugmentedInjection n (gf x)=_
    rw [gradientAugmentedInjection_apply,←WithLp.toLp_smul,←WithLp.toLp_add]
    congr 1
    ext <;> simp
  have hEB (j : ℕ) :
      (∫ x in Ω,‖(WithLp.toLp 2 (ε j,gf x) : GradientAugmentedSpace n)‖^p)=‖B j‖^p :=
    (integral_congr_ae ((hBae j).fun_comp (fun z => ‖z‖^p))).symm.trans
      (BMCompactNonlinear.lp_norm_rpow_eq_integral hp0 (B j)).symm
  have hupper (j : ℕ) : ‖A j‖^p≤‖B j‖^p+p*c*(∫ x in Ω,w j x) := by
    have hboundary : ZeroBoundarySobolevPair p Ω ((f+w j)-f) ((gf+gw j)-gf) := by
      apply (hw j).congr (Eventually.of_forall (fun x => ?_))
        (Eventually.of_forall (fun x => ?_)) <;>
          simp only [Pi.add_apply,Pi.sub_apply,add_sub_cancel_left]
    have htest := (hw j).smul_actual (-1)
    have hmin := (hu j).energy_minimality hΩb htest
    have hvec (x : Space n) : (gf+gw j) x+((-1 : ℝ) • gw j) x=gf x := by
      simp only [Pi.add_apply,Pi.smul_apply,neg_one_smul];abel
    simp_rw [hvec] at hmin
    simp only [Pi.smul_apply,neg_one_smul,integral_neg] at hmin
    have he := root_forced_physical_energy_le_augmented (ε := ε j) hf.1
      (hf.2.2.1.add (hw j).1.2.2.1)
    change (∫ x in Ω,‖(gf+gw j) x‖^p)≤_ at he
    rw [root_forced_energy_eq_lp_power hf.1 (hf.2.2.1.add (hw j).1.2.2.1),
      MemLp.toLp_add hf.2.2.1 (hw j).1.2.2.1] at he
    rw [hEB j] at hmin
    linarith only [he,hmin]
  let R := ‖C‖+‖F‖
  have hBbound (j : ℕ) : ‖B j‖≤R := by
    calc
      _≤‖ε j • C‖+‖T F‖ := norm_add_le _ _
      _=|ε j| * ‖C‖+‖F‖ := by rw [norm_smul,Real.norm_eq_abs,gradientAugmentedLpInjection_norm]
      _≤R := by dsimp only [R];nlinarith only [hεb j,norm_nonneg C]
  obtain ⟨K,hK,hload⟩ := exists_W0_source_load_bound_allp hf.1 hn hΩb
  let L : ℝ := |c| * K
  have hL : 0≤L := mul_nonneg (abs_nonneg c) hK
  let M : ℝ := R^p/p+L*‖F‖
  obtain ⟨Q,hQ0,hQ⟩ := source_energy_coercive_allp hf.1 hL M
  have hAbound (j : ℕ) : ‖A j‖≤Q := by
    have hG : ‖G j‖≤‖A j‖+‖F‖ := by
      calc
        _=‖A j-F‖ := by congr 1;dsimp only [A];abel
        _≤_ := norm_sub_le _ _
    have hl : |∫ x in Ω,w j x|≤K*‖G j‖ := by
      simpa only [G,Lp.norm_toLp] using hload (hw j)
    have hc : c*(∫ x in Ω,w j x)≤L*(‖A j‖+‖F‖) := by
      calc
        _≤|c| * |∫ x in Ω,w j x| := by simpa only [abs_mul] using le_abs_self (c*(∫ x in Ω,w j x))
        _≤|c| * (K*‖G j‖) := mul_le_mul_of_nonneg_left hl (abs_nonneg c)
        _=L*‖G j‖ := by dsimp only [L];ring
        _≤_ := mul_le_mul_of_nonneg_left hG hL
    have hR : ‖B j‖^p≤R^p := Real.rpow_le_rpow (norm_nonneg _) (hBbound j) hp0.le
    have he := hupper j
    have hc' := mul_le_mul_of_nonneg_left hc hp0.le
    have henergy : ‖A j‖^p/p-L*‖A j‖≤M := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hp0).mpr
      dsimp only [M]
      have hid : (R^p/p+L*‖F‖+L*‖A j‖)*p=R^p+p*(L*(‖A j‖+‖F‖)) := by
        field_simp [hp0.ne']
        <;> ring
      rw [hid]
      nlinarith only [he,hc',hR]
    by_contra hnot
    have hlarger := hQ ‖A j‖ (le_of_not_ge hnot)
    exact (not_lt_of_ge henergy) hlarger
  have hBlim : Tendsto B atTop (𝓝 (T F)) := by
    simpa only [B,zero_smul,zero_add] using (hε.smul_const C).add_const (T F)
  have hElim : Tendsto (fun j => ‖B j‖^p) atTop (𝓝 (‖F‖^p)) := by
    have he := hBlim.norm.rpow_const (Or.inr hp0.le)
    rw [show ‖T F‖=‖F‖ from gradientAugmentedLpInjection_norm p F] at he
    exact he
  have hnormal : Tendsto (fun j => ‖G j‖) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    let S := max Q ‖F‖
    obtain ⟨κ,hκ,hgap⟩ := BMCompactBanach.lp_bounded_midpoint_gap
      (E := Space n) (α := Space n) (μ := μ) hf.1 S δ hδ
    have hsmalllim : Tendsto (fun j => (‖B j‖^p-‖F‖^p)/2) atTop (𝓝 0) := by
      simpa only [sub_self,zero_div] using (hElim.sub_const (‖F‖^p)).div_const 2
    have hsmall : ∀ᶠ j in atTop,(‖B j‖^p-‖F‖^p)/2<κ :=
      (tendsto_order.mp hsmalllim).2 κ hκ
    filter_upwards [hsmall] with j hj
    have hlt : ‖G j‖<δ := by
      by_contra hnot
      have hdiff : A j-F=G j := by dsimp only [A];abel
      have hsep : δ≤‖A j-F‖ := by rw [hdiff];exact le_of_not_gt hnot
      have hg := hgap (A j) F ((hAbound j).trans (le_max_left _ _)) (le_max_right _ _) hsep
      have hm := root_forced_lp_midpoint_minimum hH hf (hw j) hΩb
      change ‖F‖^p+p*c*((1/2 : ℝ)*(∫ x in Ω,w j x))≤‖(1/2 : ℝ) • (A j+F)‖^p at hm
      have he := hupper j
      nlinarith only [hg,hm,he,hj]
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)] using hlt
  have hg : Tendsto (fun j=>eLpNorm (gw j) (ENNReal.ofReal p) μ) atTop (𝓝 0) := by
    have hr : Tendsto (fun j=>(eLpNorm (gw j) (ENNReal.ofReal p) μ).toReal)
        atTop (𝓝 0) := by simpa only [G,Lp.norm_toLp] using hnormal
    have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
    simp only [ENNReal.ofReal_zero] at he
    convert he using 1
    funext j
    exact (ENNReal.ofReal_toReal (hw j).1.2.2.1.eLpNorm_ne_top).symm
  obtain ⟨P,hP⟩ := exists_W0_Lp_poincare_constant_allp hf.1 hn hΩb
  have hupperlim : Tendsto (fun j=>(P : ℝ≥0∞)*eLpNorm (gw j) (ENNReal.ofReal p) μ)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hg (Or.inr ENNReal.coe_ne_top)
  exact ⟨hg,tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupperlim (fun _=>bot_le) (fun j=>hP (hw j))⟩

theorem WeakPSourcePair.exists_regularized_source_W1p_approximants
    {n : ℕ} {p c : ℝ} {Ω : Set (Space n)}
    {f : Space n → ℝ} {gf : Space n → Space n}
    (hH : WeakPSourcePair p c Ω f gf) (hf : SobolevPair p Ω f gf)
    (hn : 2≤n) (hΩb : Bornology.IsBounded Ω) :
    ∃ w : ℕ → Space n → ℝ,∃ gw : ℕ → Space n → Space n,
      (∀ j,ZeroBoundarySobolevPair p Ω (w j) (gw j)) ∧
      (∀ j : ℕ,GlobalWeakRegularizedSourcePair p (((j : ℝ)+1)⁻¹) c Ω (f+w j) (gf+gw j)) ∧
      Tendsto (fun j=>eLpNorm (gw j) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) ∧
      Tendsto (fun j=>eLpNorm (w j) (ENNReal.ofReal p) (volume.restrict Ω)) atTop (𝓝 0) := by
  choose w gw hw hu using (fun j : ℕ => exists_global_weak_regularized_Dirichlet
    hf.1 hn hH.2.1 hΩb (((j : ℝ)+1)⁻¹) c hf)
  have hεb (j : ℕ) : |((j : ℝ)+1)⁻¹|≤1 := by
    rw [abs_of_pos (inv_pos.mpr (by positivity : 0<(j : ℝ)+1))]
    exact inv_le_one_of_one_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) j])
  have hε : Tendsto (fun j : ℕ=>((j : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  obtain ⟨hg,hwlim⟩ := hH.regularized_source_family_W1p_tendsto hf hn hΩb hw hu hεb hε
  exact ⟨w,gw,hw,hu,hg,hwlim⟩

end BMCompactPDE
#print axioms BMCompactPDE.WeakPSourcePair.regularized_source_family_W1p_tendsto
#print axioms BMCompactPDE.WeakPSourcePair.exists_regularized_source_W1p_approximants
