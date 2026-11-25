import CapacityAffineEnergy
import CriticalFluxLimit
import CriticalShellCutoffs
import EquilibriumFluxMass
import ExteriorCapacityBridge
import GreenFoundation
import OuterNeighborhoodPotential
import OuterPotentialWeakLimit
import RootDilationBatch
import SingularScalarStability
import UpstreamFundamentalAllp
import UpstreamGreenScalarStability
noncomputable section
set_option autoImplicit false
open Set Metric Filter Bornology MeasureTheory InnerProductSpace
open scoped ENNReal Topology ContDiff
namespace BMCompactPDE

/-- All exponents. Uniform scalar convergence to an actual weak harmonic
profile on a bounded comparison collar forces strong gradient convergence
on every relatively compact interior region. -/
theorem harmonic_gradient_tendsto_of_uniform_comparison {n : ℕ} {p : ℝ} (hp : 1<p)
    {U D : Set (Space n)} (hU : IsOpen U) (hD : LocalDomain D U)
    {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n} {v : Space n → ℝ} {h : Space n → Space n}
    (hu : ∀ j, WeakPHarmonicPair p U (u j) (g j)) (hv : WeakPHarmonicPair p U v h)
    {B : ℝ} (hB : 0≤B) (hvB : ∀ x∈U, |v x|≤B)
    (hlim : ∀ δ : ℝ, 0<δ → ∀ᶠ j in atTop, ∀ x∈U, |u j x-v x|≤δ) :
    Tendsto (fun j => eLpNorm (g j-h) (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0) := by
  let H := fun j => ∫ x in D, ‖g j x-h x‖^p
  have hBd (j : ℕ) {δ : ℝ} (hd : δ≤1) (hj : ∀ x∈U, |u j x-v x|≤δ) (x : Space n) (hx : x∈U) :
      |u j x| ≤ B+1 := by
    have hb := abs_add_le (u j x-v x) (v x)
    rw [sub_add_cancel] at hb
    linarith only [hb,hj x hx,hvB x hx,hd]
  have hBC (x : Space n) (hx : x∈U) : |v x| ≤ B+1 := (hvB x hx).trans (by linarith)
  have hex : ∃ C q : ℝ, 0<q ∧ ∀ (j : ℕ) {δ : ℝ}, 0<δ → δ≤1 →
      (∀ x∈U, |u j x-v x|≤δ) → H j ≤ C*δ^q := by
    by_cases hp2 : p<2
    · obtain ⟨C,_,hC⟩ := exists_local_singular_gradient_stability_of_scalar_bounds hp hp2 hU hD
        (show 0≤B+1 by linarith)
      refine ⟨C,p/2,by linarith,?_⟩
      intro j δ hd hd1 hj
      exact (hC _ _ _ _ (hu j) hv (hBd j hd1 hj) hBC δ hd.le hj).2
    · obtain ⟨C,_,hC⟩ := exists_local_gradient_stability_of_scalar_bounds (le_of_not_gt hp2) hU hD
      refine ⟨C*(B+1)^(p-1),1,zero_lt_one,?_⟩
      intro j δ hd hd1 hj
      have he := (hC _ _ _ _ (hu j) hv (B+1) δ (by linarith) hd.le (hBd j hd1 hj) hBC hj).2
      rw [Real.rpow_one];convert he using 1;ring
  obtain ⟨C,q,hq,hest⟩ := hex
  have hHL : Tendsto H atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have ht : Tendsto (fun d : ℝ => C*d^q) (𝓝[>] 0) (𝓝 0) := by
      simpa only [Real.zero_rpow hq.ne',mul_zero] using
        (((Real.continuousAt_rpow_const (0:ℝ) q (Or.inr hq.le)).tendsto.const_mul C).mono_left nhdsWithin_le_nhds)
    have hpos : ∀ᶠ d : ℝ in 𝓝[>] 0, 0<d := self_mem_nhdsWithin
    have hlt : ∀ᶠ d : ℝ in 𝓝[>] 0, d<1 :=
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
    obtain ⟨δ,⟨hδ,hδ1⟩,hδε⟩ := ((hpos.and hlt).and (ht.eventually_lt_const hε)).exists
    filter_upwards [hlim δ hδ] with j hj
    have h0 : 0≤H j := integral_nonneg (fun x=>Real.rpow_nonneg (norm_nonneg _) _)
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg h0] using (hest j hδ hδ1.le hj).trans_lt hδε
  have hp0 := zero_lt_one.trans hp
  let _ : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  have he (j : ℕ) : eLpNorm (g j-h) (ENNReal.ofReal p) (volume.restrict D) = ENNReal.ofReal ((H j)^(1/p)) := by
    have hmem := ((hu j).2.2.1 D hD).2.2.1.sub ((hv.2.2.1 D hD).2.2.1)
    simpa only [ENNReal.toReal_ofReal hp0.le,one_div,Pi.sub_apply,H] using
      hmem.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top
  simp only [he]
  have hpq : 0<1/p := one_div_pos.mpr hp0
  simpa only [Function.comp_def,Real.zero_rpow hpq.ne',ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((Real.continuousAt_rpow_const (0:ℝ) (1/p) (Or.inr hpq.le)).tendsto.comp hHL))


/-- The nonlinear flux paired with a scaled cutoff is exactly invariant under
subcritical blow-down with its natural amplitude normalization. -/
theorem integral_subcritical_flux_dilate_test {n : ℕ} {p : ℝ} (hp : 1<p)
    {R : ℝ} (hR : 0<R) (g : Space n→Space n) {θ : Space n→ℝ} (hθ : ContDiff ℝ ∞ θ) :
    (∫ x, fluxPairing p (fun y=>R^(((n:ℝ)-p)/(p-1)) • R • g (R • y)) (gradient θ) x) =
    ∫ x, fluxPairing p g (gradient (BMCompactCapacityV2.dilateTest R θ)) x := by
  let α := ((n:ℝ)-p)/(p-1)
  have he : (α+1)*(p-1)=(n:ℝ)-1 := by dsimp [α]; field_simp [(sub_pos.mpr hp).ne'];ring
  let P := fluxPairing p g (gradient (BMCompactCapacityV2.dilateTest R θ))
  have hpair (x : Space n) : fluxPairing p (fun y=>R^(((n:ℝ)-p)/(p-1)) • R • g (R • y)) (gradient θ) x =
      R^n * P (R • x) := by
    have hgrad : gradient (BMCompactCapacityV2.dilateTest R θ) (R • x) = R⁻¹ • gradient θ x := by
      change gradient (fun y : Space n=>θ (R⁻¹ • y)) (R • x) = R⁻¹ • gradient θ x
      simpa only [smul_smul,inv_mul_cancel₀ hR.ne',one_smul] using
        BMCompactCapacityV2.gradient_comp_const_smul hθ R⁻¹ (R • x)
    have hpow : R^((n:ℝ)-1)=R^n*R⁻¹ := by rw [Real.rpow_sub hR,Real.rpow_natCast,Real.rpow_one,div_eq_mul_inv]
    have hpow' : (R^α*R)^(p-1)=R^n*R⁻¹ := by
      rw [←Real.rpow_add_one hR.ne',←Real.rpow_mul hR.le,he,hpow]
    change fluxPairing p (fun y=>R^α • R • g (R • y)) (gradient θ) x = R^n * P (R • x)
    simp only [P,fluxPairing,smul_smul,pFlux_nonneg_smul hp (mul_nonneg (Real.rpow_nonneg hR.le _) hR.le),
      hgrad,real_inner_smul_left,real_inner_smul_right,hpow',mul_assoc]
  simp_rw [hpair]
  rw [integral_const_mul]
  have hc := integral_comp_dilation_restrict (D:=(univ : Set (Space n))) MeasurableSet.univ hR.ne' P
  simp only [preimage_univ,Measure.restrict_univ,abs_of_pos (inv_pos.mpr (pow_pos hR n))] at hc
  rw [hc,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero n hR.ne'),one_mul]


/-- A finite positive normalized limit of an actual exterior harmonic scalar
identifies the mass of its original unscaled nonlinear flux. -/
theorem WeakPHarmonicPair.subcritical_mass_of_scalar_far_field {n : ℕ} (hn : 2≤n) {p : ℝ}
    (hp : 1<p) (hpn : p<(n:ℝ)) {K : Set (Space n)} (hK : IsCompact K)
    {u : Space n→ℝ} {g : Space n→Space n} (hg : WeakPHarmonicPair p Kᶜ u g)
    {a J : ℝ} (ha : 0<a)
    (hab : Tendsto (fun x=>‖x‖^(((n:ℝ)-p)/(p-1))*u x) (cocompact _) (𝓝 a))
    (hMass : ∀ θ : Space n→ℝ, SmoothTest univ θ → (∀x∈K, θ x=1) →
      (∫ x, fluxPairing p g (gradient θ) x)=J) :
    a^(p-1)*(((n:ℝ)-p)/(p-1))^(p-1)*canonicalSphereArea n=J := by
  let α := ((n:ℝ)-p)/(p-1)
  let σ := canonicalSphereArea n
  have hα : 0<α := div_pos (sub_pos.mpr hpn) (sub_pos.mpr hp)
  have hσ : 0<σ := canonicalSphereArea_pos (by omega)
  let P := positiveSubcriticalProfile n p
  let b := a*α*σ^((p-1)⁻¹)
  have hb : 0<b := mul_pos (mul_pos ha hα) (Real.rpow_pos_of_pos hσ _)
  have hprofile (x : Space n) : b*P x=a*‖x‖^(-α) := by
    have hpow : (p-(n:ℝ))/(p-1) = -α := by dsimp [α];ring
    change b * -(fundamentalPotential n σ p x) = _
    simp only [fundamentalPotential,if_neg hpn.ne,radialPowerPotential,hpow,inv_neg,neg_mul,neg_neg,b,Real.rpow_neg hσ.le]
    field_simp [hα.ne',(Real.rpow_pos_of_pos hσ ((p-1)⁻¹)).ne'] <;> ring
  have hbpow : b^(p-1)=a^(p-1)*α^(p-1)*σ := by
    simp only [b,Real.mul_rpow (mul_nonneg ha.le hα.le) (Real.rpow_nonneg hσ.le _),
      Real.mul_rpow ha.le hα.le,←Real.rpow_mul hσ.le,inv_mul_cancel₀ (sub_pos.mpr hp).ne',Real.rpow_one]
  let U := radialAnnulusAt n 0 1 5
  let D := radialAnnulusAt n 0 2 4
  let μ := volume.restrict D
  have hU : IsOpen U := isOpen_radialAnnulusAt _ _ _ _
  have hD : LocalDomain D U := by
    refine ⟨isOpen_radialAnnulusAt _ _ _ _,isBounded_radialAnnulusAt _ _ _ _,?_⟩
    intro x hx
    have h := bounds_of_mem_closure_radialAnnulusAt n 0 2 4 hx
    exact ⟨(by norm_num : (1:ℝ)<2).trans_le h.1,h.2.trans_lt (by norm_num)⟩
  have hxn (x : Space n) (hx : x∈U) : 1<‖x‖ := by
    simpa only [dist_zero_right] using hx.1
  have hU0 : U ⊆ ({0}ᶜ : Set (Space n)) := fun x hx=> norm_pos_iff.mp (zero_lt_one.trans (hxn x hx))
  have hF := (weakPHarmonicPair_fundamentalPotential_all_p n hσ hp).mono hU0 hU
  have hP : WeakPHarmonicPair p U P (gradient P) := by
    have heP : P = -(fundamentalPotential n σ p (E:=Space n)) := by funext x;rfl
    have heG : gradient (-(fundamentalPotential n σ p (E:=Space n))) =
        -(gradient (fundamentalPotential n σ p (E:=Space n))) := by
      funext x
      change gradient (fun z : Space n=> -fundamentalPotential n σ p z) x =
        -(gradient (fundamentalPotential n σ p (E:=Space n)) x)
      unfold gradient
      rw [fderiv_fun_neg,map_neg]
    rw [heP,heG]
    simpa only [neg_one_smul] using hF.smul (-1)
  have hPscaled := hP.smul b
  have hsmall (x : Space n) (hx : x∈U) : ‖x‖^(-α)≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (hxn x hx).le (neg_nonpos.mpr hα.le)
  have hvB (x : Space n) (hx : x∈U) : |(b • P) x|≤a := by
    simp only [Pi.smul_apply,smul_eq_mul,hprofile,abs_mul,abs_of_pos ha,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hsmall x hx) ha.le
  obtain ⟨T,hT,hTK⟩ := hK.isBounded.subset_ball_lt 0 (0:Space n)
  let R := fun j : ℕ=> T+1+(j:ℝ)
  have hRT (j : ℕ) : T<R j := by dsimp [R];linarith only [Nat.cast_nonneg (α:=ℝ) j]
  have hR (j : ℕ) := hT.trans (hRT j)
  have hRt : Tendsto R atTop atTop := tendsto_atTop_add_const_left atTop (T+1) tendsto_natCast_atTop_atTop
  let w := fun j : ℕ=>fun x : Space n=>(R j)^α*u (R j • x)
  let G := fun j : ℕ=>fun x : Space n=>(R j)^α • R j • g (R j • x)
  have hnorm (j : ℕ) (x : Space n) : ‖R j • x‖=R j*‖x‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hR j)]
  have hlarge (j : ℕ) (x : Space n) (hx : x∈U) : R j<‖R j • x‖ := by
    rw [hnorm];simpa only [mul_one] using mul_lt_mul_of_pos_left (hxn x hx) (hR j)
  have hweak (j : ℕ) : WeakPHarmonicPair p U (w j) (G j) := by
    have hd := hg.source_zero.dilation_actual (hR j)
    rw [mul_zero] at hd
    have hsub : U ⊆ (fun x : Space n=> R j • x) ⁻¹' Kᶜ := by
      intro x hx hxK
      have hlt : ‖R j • x‖<T := by simpa only [mem_ball,dist_zero_right] using hTK hxK
      exact (not_lt_of_ge ((hRT j).trans (hlarge j x hx)).le) hlt
    exact (hd.harmonic_of_source_zero.mono hsub hU).smul ((R j)^α)
  have huni (ε : ℝ) (hε : 0<ε) : ∀ᶠ j in atTop, ∀ x∈U, |w j x - (b • P) x|≤ε := by
    rw [←Metric.cobounded_eq_cocompact] at hab
    obtain ⟨S,_,hS⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp
      (Metric.tendsto_nhds.mp hab ε hε)
    filter_upwards [hRt.eventually (eventually_gt_atTop S)] with j hj
    intro x hx
    have hx0 := zero_lt_one.trans (hxn x hx)
    have hpoint := hS (show R j • x ∈ {z : Space n | S≤‖z‖} from (hj.trans (hlarge j x hx)).le)
    rw [Real.dist_eq] at hpoint
    change |(R j)^α*u (R j • x)-b*P x|≤ε
    have he : (R j)^α*u (R j • x)-b*P x = ‖x‖^(-α)*(‖R j • x‖^α*u (R j • x)-a) := by
      rw [hprofile,hnorm,Real.mul_rpow (hR j).le (norm_nonneg _),Real.rpow_neg hx0.le]
      field_simp [(Real.rpow_pos_of_pos hx0 α).ne'] <;> ring
    rw [he,abs_mul,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact (mul_le_mul_of_nonneg_right (hsmall x hx) (abs_nonneg _)).trans (by simpa only [one_mul] using hpoint.le)
  have hgrad := harmonic_gradient_tendsto_of_uniform_comparison hp hU hD hweak hPscaled ha.le hvB huni
  obtain ⟨_,_,hθ⟩ := exists_critical_shell_cutoffs n (by omega)
  obtain ⟨θ,hθd,hθc,_,hθ1,_,hθgrad,_,_⟩ := hθ 1 zero_lt_one
  have hoff (x : Space n) (hx : x∉D) : gradient θ x=0 := hθgrad x (by simpa only [mul_one] using hx)
  have hglobal (v : Space n→Space n) : (∫ x in D,fluxPairing p v (gradient θ) x)=
      ∫ x,fluxPairing p v (gradient θ) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>by simp only [fluxPairing,hoff x hx,inner_zero_right])
  have hJ (j : ℕ) : (∫ x,inner ℝ (pFlux p (G j x)) (gradient θ x) ∂μ)=J := by
    change (∫ x in D,fluxPairing p (G j) (gradient θ) x)=J
    rw [hglobal,integral_subcritical_flux_dilate_test hp (hR j) g hθd]
    apply hMass _ ⟨BMCompactCapacityV2.contDiff_dilateTest hθd _,BMCompactCapacityV2.hasCompactSupport_dilateTest hθc (hR j).ne',subset_univ _⟩
    intro x hx
    apply hθ1
    have hx' : ‖x‖<T := by simpa only [mem_ball,dist_zero_right] using hTK hx
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hR j)),←div_eq_inv_mul,mul_one]
    exact ((div_lt_one (hR j)).mpr (hx'.trans (hRT j))).le.trans (by norm_num)
  have hθLp : MemLp (gradient θ) (ENNReal.ofReal p) μ :=
    (BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p) hθd hθc).restrict D
  have hL := flux_pairing_constant_of_strong_Lp_limit hp (fun j=>((hweak j).2.2.1 D hD).2.2.1)
    ((hPscaled.2.2.1 D hD).2.2.1) hθLp hgrad (Eventually.of_forall hJ)
  change (∫ x in D,fluxPairing p (b • gradient P) (gradient θ) x)=J at hL
  rw [hglobal] at hL
  have hsource := ((positiveSubcriticalProfile_unit_source hn hp hpn).2.2 θ hθd hθc).2
  rw [show θ 0=1 from hθ1 0 (by simp)] at hsource
  simpa only [fluxPairing,Pi.smul_apply,pFlux_nonneg_smul hp hb.le,real_inner_smul_left,integral_const_mul,
    P,hsource,mul_one,hbpow] using hL


/-- Any finite positive power-law far-field coefficient of the actual
continuous potential of a positive closed neighbourhood determines its
original smooth-test variational capacity. -/
theorem ContinuousUnitCapacityData.subcritical_neighborhood_mass_of_far_field {n : ℕ} (hn : 2≤n)
    {p : ℝ} (hp : 1<p) (hpn : p<(n:ℝ)) {K : Set (Space n)} (hK : IsCompact K) {δ : ℝ}
    (hδ : 0<δ) (U : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood δ K))
    {a : ℝ} (ha : 0<a)
    (hab : Tendsto (fun x=>‖x‖^(((n:ℝ)-p)/(p-1))*U.scalar x) (cocompact _) (𝓝 a)) :
    a^(p-1)*(((n:ℝ)-p)/(p-1))^(p-1)*canonicalSphereArea n =
      (BMCompactCapacityV2.variationalCapacity p (BMCompact.closedNeighborhood δ K)).toReal := by
  let L := BMCompact.closedNeighborhood δ K
  have hL : IsCompact L := BMCompact.isCompact_closedNeighborhood hK δ
  let q := (n:ℝ)*p/((n:ℝ)-p)
  let _ : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  let _ : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr (by
    apply (le_div_iff₀ (sub_pos.mpr hpn)).mpr
    nlinarith only [mul_nonneg (show 0≤(n:ℝ) by positivity) (sub_nonneg.mpr hp.le),hp])⟩
  obtain ⟨w,hw,hm⟩ := exists_exteriorCapacityClass_minimum p q hp hpn rfl hL
  obtain ⟨v,g,hc,hunit,hv,hg,_,hH,hbounds,hdec,hen,happ⟩ :=
    exists_continuous_unit_capacity_potential_closedNeighborhood hp hpn hK hδ
  let V : ContinuousUnitCapacityData p L := ⟨v,g,hc,hunit,hv,hH,hbounds,hdec,hen⟩
  have huv : U.scalar = v := funext (fun x => le_antisymm
    (U.le_of_subset hn hL Subset.rfl V x) (V.le_of_subset hn hL Subset.rfl U x))
  have he := capacity_eq_exteriorCapacityClass_minimum_energy _ _ hp hw hm
  rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)] at he
  have hga := (variational_capacity_potentials_ae_unique hp hpn hL hv hg
    (Lp.memLp w.1.1) (Lp.memLp w.1.2) hen he happ (exteriorCapacityClass_smooth_approximation p q hw)).2
  apply hH.subcritical_mass_of_scalar_far_field hn hp hpn hL ha (huv ▸ hab)
  intro θ hθ hone
  have hmass := exteriorCapacity_minimum_flux_mass p q hp hw hm hθ hone
  change (∫ y,inner ℝ (pFlux p (g y)) (gradient θ y)) = (BMCompactCapacityV2.variationalCapacity p L).toReal
  rw [integral_congr_ae (hga.mono (fun y hy =>
    congrArg (fun z => inner ℝ (pFlux p z) (gradient θ y)) hy)),←hmass.2,
    ENNReal.toReal_ofReal (hmass.1.symm ▸ integral_nonneg (fun y => Real.rpow_nonneg (norm_nonneg _) _))]
end BMCompactPDE
#print axioms BMCompactPDE.harmonic_gradient_tendsto_of_uniform_comparison
#print axioms BMCompactPDE.integral_subcritical_flux_dilate_test
#print axioms BMCompactPDE.WeakPHarmonicPair.subcritical_mass_of_scalar_far_field
#print axioms BMCompactPDE.ContinuousUnitCapacityData.subcritical_neighborhood_mass_of_far_field
