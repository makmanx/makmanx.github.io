import CriticalShellCutoffs
import CriticalShellFlux
import RadialWeakHarmonic

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric Bornology
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- Uniform in the outer endpoint, with a single fixed inner endpoint.
Consequently the number of intervening dyadic shells never enters the bound. -/
theorem WeakPHarmonicPair.uniform_critical_green_difference_windows
    {n : ℕ} (hn : 2 ≤ n) {σ : ℝ} (hσ : 0<σ) {K : Set (Space n)} (hK : IsCompact K)
    {u : Space n → ℝ} {g : Space n → Space n} (hu : WeakPHarmonicPair (n:ℝ) Kᶜ u g)
    (hrem : HasBoundedGreenRemainder n σ n u) :
    ∃ S C : ℝ, 0<S ∧ 0≤C ∧ ∀ R : ℝ, 2*S≤R →
      IntegrableOn (fun x => ‖(1/2:ℝ) • (g x-gradient (fundamentalPotential n σ n) x)‖^n)
        (radialAnnulusAt n 0 (4*S) (2*R)) volume ∧
      (∫ x in radialAnnulusAt n 0 (4*S) (2*R),
        ‖(1/2:ℝ) • (g x-gradient (fundamentalPotential n σ n) x)‖^n) ≤ C := by
  have hp : 1 < (n : ℝ) := by exact_mod_cast (show 1<n by omega)
  let F := fundamentalPotential n σ (n:ℝ) (E:=Space n)
  let h := gradient F
  have hf := weakPHarmonicPair_fundamentalPotential n hσ hp (le_refl (n:ℝ))
  have hf0 : WeakPHarmonicPair (n:ℝ) ({0} : Set (Space n))ᶜ F h :=
    hf.mono (fun x hx hx0 => hx (mem_singleton_iff.mpr hx0)) isClosed_singleton.isOpen_compl
  have hremF : HasBoundedGreenRemainder n σ n F := ⟨0,le_rfl,Eventually.of_forall (fun x=>by simp [F])⟩
  obtain ⟨E,hE,hEg⟩ := hu.uniform_critical_green_annular_energy hn hσ hK hrem
  obtain ⟨L,hL,hLh⟩ := hf0.uniform_critical_green_annular_energy hn hσ isCompact_singleton hremF
  obtain ⟨b,hb⟩ := eventually_atTop.mp (hEg.and hLh)
  obtain ⟨A,hA,hAinf⟩ := hrem
  obtain ⟨t,_,ht⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp hAinf
  obtain ⟨k,_,hk⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space n)
  let S := 1+max 0 (max b (max k t))
  have hS : 0 < S := by dsimp [S]; linarith only [le_max_left (0:ℝ) (max b (max k t))]
  have hbS : b ≤ S := by dsimp [S]; grind
  have hkS : k < S := by dsimp [S]; grind
  have htS : t ≤ S := by dsimp [S]; grind
  let Ω := Kᶜ ∩ {x : Space n | x≠0}
  have hΩ : IsOpen Ω := hK.isClosed.isOpen_compl.inter isOpen_ne
  have huΩ := (hu.mono (inter_subset_left : Ω⊆Kᶜ) hΩ).source_zero
  have hfΩ := (hf.mono (inter_subset_right : Ω⊆{x : Space n | x≠0}) hΩ).source_zero
  have haway (x : Space n) (hx : S ≤ ‖x‖) : x ∈ Ω := by
    refine ⟨fun hxK => ?_,norm_pos_iff.mp (hS.trans_le hx)⟩
    have hsmall : ‖x‖ < k := by simpa only [mem_ball,dist_zero_right] using hk hxK
    linarith only [hkS,hx,hsmall]
  obtain ⟨P,hP,hcut⟩ := exists_critical_shell_cutoffs n (by omega)
  let M := A*(E+L+2*P)
  have hM : 0 ≤ M := by dsimp [M];positivity
  refine ⟨S,(n:ℝ)*(2*M)/4,hS,by positivity,?_⟩
  intro R hRS
  have hSR : S ≤ R := by linarith only [hRS,hS]
  have hR := hS.trans_le hSR
  let V := radialAnnulusAt n 0 S (5*R)
  let D := radialAnnulusAt n 0 (4*S) (2*R)
  have hV : LocalDomain V Ω := by
    refine ⟨isOpen_radialAnnulusAt _ _ _ _,isBounded_radialAnnulusAt _ _ _ _,?_⟩
    intro x hx
    apply haway
    simpa only [dist_zero_right] using (bounds_of_mem_closure_radialAnnulusAt n 0 S (5*R) hx).1
  have hDV : D ⊆ V := by
    intro x hx
    exact ⟨(by linarith only [hS] : S<4*S).trans hx.1,hx.2.trans (by linarith only [hR])⟩
  let W := fun s : ℝ => radialAnnulusAt n (0:Space n) (2*s) (4*s)
  let J := fun (φ : Space n → ℝ) (x : Space n) => (u x-F x)*
    inner ℝ (pFlux n (g x)-pFlux n (h x)) (gradient φ x)
  have htrans (s : ℝ) (hs : S≤s) (hsR : s≤R) (φ : Space n → ℝ)
      (hc : ContDiff ℝ ∞ φ) (hoff : ∀ x, x∉W s → gradient φ x=0)
      (hI : Integrable (fun x=>‖gradient φ x‖^n) volume)
      (hIp : (∫ x, ‖gradient φ x‖^n ∂volume)=P) :
      IntegrableOn (fun x => |J φ x|) V volume ∧ (∫ x in V,|J φ x|) ≤ M := by
    have hs0 := hS.trans_le hs
    have hW : LocalDomain (W s) Ω := by
      refine ⟨isOpen_radialAnnulusAt _ _ _ _,isBounded_radialAnnulusAt _ _ _ _,?_⟩
      intro x hx
      apply haway
      have hh : 2*s ≤ ‖x‖ := by simpa only [dist_zero_right] using
        (bounds_of_mem_closure_radialAnnulusAt n 0 (2*s) (4*s) hx).1
      linarith only [hh,hs,hS]
    have hWV : W s ⊆ V := by
      intro x hx
      exact ⟨(by linarith only [hs,hS] : S<2*s).trans hx.1,hx.2.trans (by linarith only [hsR,hR])⟩
    have hgap (x : Space n) (hx : x∈W s) : |u x - F x|≤A := by
      apply ht
      show t ≤ ‖x‖
      have hh : 2*s < ‖x‖ := by simpa only [dist_zero_right] using hx.1
      linarith only [hh,hs,hS,htS]
    obtain ⟨hi,he⟩ := critical_shell_flux_error_bound hn hW.1 hWV hV.1.measurableSet
      (huΩ.2.2.1 _ hW) (hfΩ.2.2.1 _ hW) hA hgap
      (BMCompactCapacityV2.continuous_gradient_of_contDiff hc) hoff hI
    refine ⟨hi,he.trans ?_⟩
    rw [hIp]
    apply mul_le_mul_of_nonneg_left _ hA
    exact add_le_add_left (add_le_add (hb s (hbS.trans hs)).1 (hb s (hbS.trans hs)).2) _
  obtain ⟨a,ha,hac,hab,ha1,ha0,hag,haI,haP⟩ := hcut S hS
  obtain ⟨d,hd,hdc,hdb,hd1,hd0,hdg,hdI,hdP⟩ := hcut R hR
  obtain ⟨hJaI,hJa⟩ := htrans S le_rfl hSR a ha hag haI haP
  obtain ⟨hJdI,hJd⟩ := htrans R hSR le_rfl d hd hdg hdI hdP
  let χ := d-a
  have hχ0 (x : Space n) : 0 ≤ χ x := by
    change 0 ≤ d x-a x
    by_cases hx : ‖x‖ ≤ 2*R
    · rw [hd1 x hx];exact sub_nonneg.mpr (hab x).2
    · rw [ha0 x (by linarith only [lt_of_not_ge hx,hRS]),sub_zero];exact (hdb x).1
  have hχ1 (x : Space n) (hx : x∈D) : χ x=1 := by
    have hnorm : 4*S < ‖x‖ ∧ ‖x‖ < 2*R := by
      simpa only [D,radialAnnulusAt,mem_ofPred_eq,dist_zero_right] using hx
    simp only [χ,Pi.sub_apply,hd1 x hnorm.2.le,ha0 x hnorm.1.le,sub_zero]
  have hχS : SmoothTest V χ := by
    refine ⟨hd.sub ha,hdc.sub hac,?_⟩
    have hsupp : Function.support χ ⊆ {x | 2*S ≤ ‖x‖ ∧ ‖x‖ ≤ 4*R} := by
      intro x hx
      constructor
      · by_contra! hh
        exact hx (by simp only [χ,Pi.sub_apply,ha1 x hh.le,hd1 x (by linarith only [hh,hSR]),sub_self])
      · by_contra! hh
        exact hx (by simp only [χ,Pi.sub_apply,hd0 x hh.le,ha0 x (by linarith only [hh,hSR]),sub_self])
    have hts := closure_minimal hsupp ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    intro x hx
    have hbnd := hts hx
    change 2*S ≤ ‖x‖ ∧ ‖x‖ ≤ 4*R at hbnd
    change S < dist x 0 ∧ dist x 0 < 5*R
    rw [dist_zero_right]
    constructor <;> linarith only [hbnd.1,hbnd.2,hS,hR]
  have hgrad (x : Space n) : gradient χ x = gradient d x-gradient a x := by
    simp only [χ,gradient,fderiv_sub (hd.differentiable (by simp) x) (ha.differentiable (by simp) x),map_sub]
  have hJ := huΩ.local_flux_difference_identity hfΩ hV hχS
  have hJineq : -(∫ x in V, J χ x) ≤ 2*M := by
    have hcmp := integral_mono_ae hJ.2.1.neg (hJdI.add hJaI) (by
      filter_upwards with x
      change -(J χ x) ≤ |J d x|+|J a x|
      have heq : J χ x=J d x-J a x := by simp only [J,hgrad,inner_sub_right,mul_sub]
      rw [heq]
      linarith only [neg_le_abs (J d x),le_abs_self (J a x)])
    change (∫ x in V,-J χ x) ≤ (∫ x in V, |J d x| + |J a x|) at hcmp
    rw [integral_neg,integral_add hJdI hJaI] at hcmp
    linarith only [hcmp,hJd,hJa]
  let Z := fun x : Space n => ‖(1/2:ℝ) • (g x - h x)‖^n
  have hZI : IntegrableOn Z V volume := by
    have hgV := (((huΩ.2.2.1 _ hV).2.2.1).sub (hfΩ.2.2.1 _ hV).2.2.1).const_smul (1/2:ℝ)
    simpa only [Z,h,IntegrableOn,Pi.smul_apply,Pi.sub_apply,Real.rpow_natCast] using
      integrable_norm_rpow_of_memLp hp hgV
  have hZIw : IntegrableOn (fun x => χ x*Z x) V volume := by
    have htop := hχS.1.continuous.memLp_top_of_hasCompactSupport hχS.2.1 (volume.restrict V)
    simpa only [IntegrableOn,Pi.mul_apply,mul_comm] using! hZI.mul_of_top_right htop
  have hdom : (∫ x in D,Z x) ≤ ∫ x in V,χ x*Z x := by
    calc
      _ = ∫ x in D,χ x*Z x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (isOpen_radialAnnulusAt n 0 (4*S) (2*R)).measurableSet] with x hx
        rw [hχ1 x hx,one_mul]
      _ ≤ _ := integral_mono_measure (Measure.restrict_mono_set volume hDV)
        (Eventually.of_forall (fun x=>mul_nonneg (hχ0 x) (pow_nonneg (norm_nonneg _) n))) hZIw
  have henergy := huΩ.local_gradient_difference_bound hfΩ (by exact_mod_cast hn) hV hχS hχ0
  simp only [Real.rpow_natCast] at henergy
  change 4*(∫ x in V,χ x*Z x) ≤ -(n:ℝ)*(∫ x in V,J χ x) at henergy
  refine ⟨hZI.mono_set hDV,?_⟩
  have herr := mul_le_mul_of_nonneg_left hJineq (Nat.cast_nonneg n)
  change (∫ x in D,Z x) ≤ _
  linarith only [hdom,henergy,herr]

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.uniform_critical_green_difference_windows
