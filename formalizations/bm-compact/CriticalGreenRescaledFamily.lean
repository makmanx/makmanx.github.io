import CriticalGreenFiniteDifferenceEnergy
import GreenRemainderEnclosure

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric Bornology
open scoped Topology ENNReal
namespace BMCompactPDE

/-- The same dilations give bounded normalized n-harmonic data and vanishing
strong Lⁿ norm of the actual remainder gradient on the fixed annulus 2<|x|<7. -/
theorem IsExteriorGreen.exists_critical_rescaled_family_with_vanishing_defect
    {n : ℕ} {σ : ℝ} {K : Set (Space n)} {u : Space n → ℝ} (hu : IsExteriorGreen n σ n K u) :
    let F : Space n → ℝ := fundamentalPotential n σ n
    let U := radialAnnulusAt n 0 2 7
    ∃ R : ℕ → ℝ, ∃ V : ℕ → Space n → ℝ, ∃ Γ H : ℕ → Space n → Space n,
      (∀ j,0<R j) ∧ Tendsto R atTop atTop ∧
      (∀ j,WeakPHarmonicPair (n:ℝ) U (V j) (Γ j)) ∧
      (∀ j,SobolevPair (n:ℝ) U (V j) (Γ j)) ∧ (∀ j,Continuous (V j)) ∧
      (∃ B : ℝ, 0≤B ∧ ∀ j x, x∈U → |V j x|≤B ∧ |u (R j • x)-F (R j • x)|≤B) ∧
      (∃ M N : ℝ, 0≤M ∧ 0≤N ∧ ∀ j,
        (eLpNorm (V j) (ENNReal.ofReal (n:ℝ)) (volume.restrict U)).toReal ≤ M ∧
        (eLpNorm (Γ j) (ENNReal.ofReal (n:ℝ)) (volume.restrict U)).toReal ≤ N) ∧
      (∀ j x, x∈U → V j x-F x = u (R j • x)-F (R j • x)) ∧
      (∀ j, SobolevPair (n:ℝ) U (fun x => V j x-F x) (H j)) ∧
      Tendsto (fun j=>(eLpNorm (H j) (ENNReal.ofReal (n:ℝ)) (volume.restrict U)).toReal)
        atTop (𝓝 0) := by
  dsimp only
  obtain ⟨hp,_,hσ,hK,_,huc,_,⟨g,hg⟩,hrem⟩ := hu
  have hnNat : 1<n := by exact_mod_cast hp
  have hn : 2≤n := by omega
  let F := fundamentalPotential n σ (n:ℝ) (E:=Space n)
  let h := gradient F
  let Z := fun x : Space n => ‖g x-h x‖^n
  obtain ⟨⟨s,hs,hzI⟩,hzt⟩ := hg.finite_critical_green_gradient_difference_energy hn hσ hK hrem
  obtain ⟨A,hA,hAb⟩ := hrem
  obtain ⟨t,_,ht⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hAb
  obtain ⟨k,_,hk⟩ := hK.isBounded.subset_ball_lt 0 (0:Space n)
  let T := 1+max 0 (max s (max t k))
  have hT : 0<T := by dsimp [T];grind
  have hsT : s<T := by dsimp [T];grind
  have htT : t<T := by dsimp [T];grind
  have hkT : k<T := by dsimp [T];grind
  let R := fun j : ℕ => T+(j:ℝ)
  have hTR (j : ℕ) : T ≤ R j := le_add_of_nonneg_right (Nat.cast_nonneg j)
  have hR (j : ℕ) := hT.trans_le (hTR j)
  have hRt : Tendsto R atTop atTop := tendsto_atTop_add_const_left atTop T tendsto_natCast_atTop_atTop
  let O := radialAnnulusAt n 0 1 8
  let U := radialAnnulusAt n 0 2 7
  have hO := isOpen_radialAnnulusAt n (0:Space n) 1 8
  have hU : LocalDomain U O := by
    refine ⟨isOpen_radialAnnulusAt _ _ _ _,isBounded_radialAnnulusAt _ _ _ _,?_⟩
    intro x hx
    have hbounds := bounds_of_mem_closure_radialAnnulusAt n (0:Space n) 2 7 hx
    exact ⟨(by norm_num : (1:ℝ)<2).trans_le hbounds.1,hbounds.2.trans_lt (by norm_num)⟩
  have hUO : U ⊆ O := subset_closure.trans hU.2.2
  let c := fun j => σ ^ (-((n:ℝ)-1)⁻¹)*Real.log (R j)
  let V := fun j (x : Space n) => u (R j • x)+(-c j)
  let Γ := fun j (x : Space n) => R j • g (R j • x)
  let H := fun j (x : Space n) => R j • (g (R j • x) - h (R j • x))
  have hnorm (x : Space n) (hx : x∈O) : 1 < ‖x‖ ∧ ‖x‖ < 8 := by
    simpa only [O,radialAnnulusAt,mem_ofPred_eq,dist_zero_right] using hx
  have hRnorm (j : ℕ) (x : Space n) (hx : x∈O) : R j < ‖R j • x‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hR j)]
    simpa only [mul_one] using mul_lt_mul_of_pos_left (hnorm x hx).1 (hR j)
  have hRx (j : ℕ) (x : Space n) (hx : x∈O) : R j • x ∉ K := by
    intro hbad
    have hsmall : ‖R j • x‖ < k := by simpa only [mem_ball,dist_zero_right] using hk hbad
    linarith only [hsmall,hkT,hTR j,hRnorm j x hx]
  have hraw (j : ℕ) : WeakPHarmonicPair (n:ℝ) O (fun x=>u (R j • x)) (Γ j) := by
    have hz := hg.source_zero.dilation_actual (hR j)
    rw [mul_zero] at hz
    exact hz.harmonic_of_source_zero.mono (fun x hx=>hRx j x hx) hO
  have hV (j : ℕ) : WeakPHarmonicPair (n:ℝ) O (V j) (Γ j) := (hraw j).add_const (-c j)
  have hVc (j : ℕ) : Continuous (V j) := (huc.comp (continuous_const_smul (R j))).add continuous_const
  have hf := weakPHarmonicPair_fundamentalPotential n hσ hp (le_refl (n:ℝ))
  have hrawF (j : ℕ) : WeakPHarmonicPair (n:ℝ) O
      (fun x=>F (R j • x)) (fun x=>R j • h (R j • x)) := by
    have hz := hf.source_zero.dilation_actual (hR j)
    rw [mul_zero] at hz
    exact hz.harmonic_of_source_zero.mono (fun x hx=>norm_pos_iff.mp ((hR j).trans (hRnorm j x hx))) hO
  have hid (j : ℕ) (x : Space n) (hx : x∈O) : V j x-F x=u (R j • x)-F (R j • x) := by
    have he := fundamentalPotential_dilate_critical n σ (hR j) (norm_pos_iff.mp (zero_lt_one.trans (hnorm x hx).1))
    change F (R j • x)=F x+c j at he
    dsimp only [V]
    linarith only [he]
  let f := fundamentalRadialValue n σ (n:ℝ)
  let B := A+|f 1|+|f 8|
  have hB : 0≤B := add_nonneg (add_nonneg hA (abs_nonneg _)) (abs_nonneg _)
  have hbounds (j : ℕ) (x : Space n) (hx : x∈O) : |V j x|≤B ∧ |u (R j • x)-F (R j • x)|≤B := by
    have hremj := ht (show t ≤ ‖R j • x‖ from htT.le.trans ((hTR j).trans (hRnorm j x hx).le))
    change |u (R j • x)-F (R j • x)| ≤ A at hremj
    have h1 := fundamentalRadialValue_mono_positive n hp le_rfl hσ zero_lt_one (hnorm x hx).1.le
    have h8 := fundamentalRadialValue_mono_positive n hp le_rfl hσ (zero_lt_one.trans (hnorm x hx).1) (hnorm x hx).2.le
    rw [fundamentalPotential_norm] at h1 h8
    change f 1≤F x at h1
    change F x≤f 8 at h8
    have hdiff := hid j x hx
    dsimp only [B]
    constructor
    · apply abs_le.mpr
      constructor <;> linarith only [h1,h8,hdiff,(abs_le.mp hremj).1,(abs_le.mp hremj).2,
        neg_le_abs (f 1),le_abs_self (f 8),abs_nonneg (f 1),abs_nonneg (f 8)]
    · linarith only [hremj,abs_nonneg (f 1),abs_nonneg (f 8)]
  obtain ⟨C,hC,hest⟩ := exists_local_gradient_norm_bound_of_scalar_bound hp hO hU
  let μ := volume.restrict U
  let q := ENNReal.ofReal (n:ℝ)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hU.2.1.measure_lt_top.ne
  have hsup (j : ℕ) : (eLpNorm (V j) q μ).toReal ≤ (eLpNorm (fun _ : Space n=>B) q μ).toReal := by
    apply ENNReal.toReal_mono ((memLp_const B (μ:=μ) (p:=q)).eLpNorm_ne_top)
    apply eLpNorm_mono_ae
    filter_upwards [ae_restrict_mem hU.1.measurableSet] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hB] using (hbounds j x (hUO hx)).1
  have hSob (j : ℕ) : SobolevPair (n:ℝ) U (fun x=>V j x-F x) (H j) := by
    have huS := (hraw j).2.2.1 U hU
    have hfS := (hrawF j).2.2.1 U hU
    apply SobolevPair.congr (SobolevPair.add huS (SobolevPair.smul hfS (-1)))
    · filter_upwards [ae_restrict_mem hU.1.measurableSet] with x hx
      simpa only [Pi.add_apply,Pi.smul_apply,neg_one_smul,Pi.neg_apply,← sub_eq_add_neg] using
        (hid j x (hUO hx)).symm
    · exact Eventually.of_forall (fun x => by
        change R j • g (R j • x) + (-1:ℝ) • (R j • h (R j • x)) = R j • (g (R j • x)-h (R j • x))
        rw [neg_one_smul,smul_sub,sub_eq_add_neg])
  have henergy (j : ℕ) : (∫ x in U,‖H j x‖^n) ≤ ∫ y in {x : Space n | R j < ‖x‖}, Z y := by
    let Q := radialAnnulusAt n 0 (2*R j) (7*R j)
    have hpre : (fun x : Space n => R j • x) ⁻¹' Q = U := by
      ext x
      simp only [U,Q,radialAnnulusAt,mem_preimage,mem_ofPred_eq,dist_zero_right,norm_smul,
        Real.norm_eq_abs,abs_of_pos (hR j),mul_comm (2:ℝ) (R j),mul_comm (7:ℝ) (R j),
        mul_lt_mul_iff_right₀ (hR j)]
    have hchange := integral_comp_dilation_restrict (isOpen_radialAnnulusAt n 0 (2*R j) (7*R j)).measurableSet
      (hR j).ne' Z
    change (∫ x in (fun x : Space n => R j • x) ⁻¹' Q,Z (R j • x)) =
      |((R j)^n)⁻¹| * ∫ y in Q,Z y at hchange
    rw [hpre,abs_of_pos (inv_pos.mpr (pow_pos (hR j) n))] at hchange
    have heq : (∫ x in U,‖H j x‖^n) = ∫ y in Q,Z y := by
      change (∫ x in U, ‖R j • (g (R j • x)-h (R j • x))‖^n) = _
      simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (hR j),mul_pow,integral_const_mul]
      change (R j)^n * (∫ x in U,Z (R j • x)) = _
      rw [hchange,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero n (hR j).ne'),one_mul]
    rw [heq]
    have hsub : Q ⊆ {x : Space n | R j < ‖x‖} := by
      intro y hy
      have hh : 2*R j < ‖y‖ := by simpa only [dist_zero_right] using hy.1
      change R j < ‖y‖
      linarith only [hR j,hh]
    have htailI : IntegrableOn Z {x : Space n | R j < ‖x‖} volume :=
      hzI.mono_set (fun _ hx => lt_trans (hsT.trans_le (hTR j)) hx)
    exact integral_mono_measure (Measure.restrict_mono_set volume hsub)
      (Eventually.of_forall (fun _=>pow_nonneg (norm_nonneg _) _)) htailI
  have hEk : Tendsto (fun j=>∫ x in U,‖H j x‖^n) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hzt.comp hRt)
      (fun _=>integral_nonneg (fun _=>pow_nonneg (norm_nonneg _) _)) henergy
  have hnR : 0<(n:ℝ) := zero_lt_one.trans hp
  have hnormID (j : ℕ) : (eLpNorm (H j) q μ).toReal = (∫ x in U,‖H j x‖^n)^((n:ℝ)⁻¹) := by
    have hI : 0 ≤ ∫ x in U, ‖H j x‖^n := integral_nonneg (fun _=>pow_nonneg (norm_nonneg _) _)
    rw [(hSob j).2.2.1.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_ne_zero_iff.mpr hnR)
      ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal hnR.le,Real.rpow_natCast,ENNReal.toReal_ofReal (Real.rpow_nonneg hI _)]
  refine ⟨R,V,Γ,H,hR,hRt,fun j=>(hV j).mono hUO hU.1,fun j=>(hV j).2.2.1 U hU,hVc,
    ⟨B,hB,fun j x hx=>hbounds j x (hUO hx)⟩,
    ⟨_,_,ENNReal.toReal_nonneg,mul_nonneg hC hB,fun j=>⟨hsup j,hest _ _ (hV j) B hB
      (fun x hx=>(hbounds j x hx).1)⟩⟩,fun j x hx=>hid j x (hUO hx),hSob,?_⟩
  change Tendsto (fun j=>(eLpNorm (H j) q μ).toReal) atTop (𝓝 0)
  simp_rw [hnormID]
  simpa only [Real.zero_rpow (inv_ne_zero hnR.ne')] using hEk.rpow_const (Or.inr (inv_nonneg.mpr hnR.le))

end BMCompactPDE
#print axioms BMCompactPDE.IsExteriorGreen.exists_critical_rescaled_family_with_vanishing_defect
