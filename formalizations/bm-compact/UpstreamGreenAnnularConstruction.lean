import UpstreamGreenAnnularComparison
import UpstreamBoundarySupercriticalCondenser
import UpstreamFundamentalSphere
import RadialGlobalContinuity
import RadialWeakHarmonic
import BallGreenOrder
import WeakHarmonicScaling

/-! Actual canonical annular Green approximants above the dimension, obtained
from constructed unit-trace relative condensers. Bounded continuous WEAK
comparison derives the fundamental upper barrier; no C1 or candidate bound is
assumed. The raw gradient is the genuine scaled condenser gradient. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

private theorem annular_fundamental_nonneg {n : ℕ} {σ p : ℝ}
    (hn : 1<(n:ℝ)) (hnp : (n:ℝ)<p) (hσ : 0<σ) (x : Space n) :
    0≤fundamentalPotential n σ p x := by
  let q : ℝ := (p-(n:ℝ))/(p-1)
  have hq : 0<q := div_pos (sub_pos.mpr hnp) (sub_pos.mpr (hn.trans hnp))
  simp only [fundamentalPotential,if_neg (ne_of_gt hnp),radialPowerPotential]
  change 0≤q⁻¹*σ^(-(p-1)⁻¹)*‖x‖^q
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hq.le) (Real.rpow_nonneg hσ.le _))
    (Real.rpow_nonneg (norm_nonneg _) _)

private theorem annular_radial_value_pos {n : ℕ} {σ p R : ℝ}
    (hn : 1<(n:ℝ)) (hnp : (n:ℝ)<p) (hσ : 0<σ) (hR : 0<R) :
    0<fundamentalRadialValue n σ p R := by
  let q : ℝ := (p-(n:ℝ))/(p-1)
  have hq : 0<q := div_pos (sub_pos.mpr hnp) (sub_pos.mpr (hn.trans hnp))
  simp only [fundamentalRadialValue,fundamentalPotential,if_neg (ne_of_gt hnp),radialPowerPotential,
    Real.norm_eq_abs,abs_of_pos hR]
  change 0<q⁻¹*σ^(-(p-1)⁻¹)*R^q
  exact mul_pos (mul_pos (inv_pos.mpr hq) (Real.rpow_pos_of_pos hσ _)) (Real.rpow_pos_of_pos hR _)

set_option maxHeartbeats 1000000 in
theorem exists_canonical_annular_green_approximant_supercritical
    {n : ℕ} {p : ℝ} (hn : 2≤n) (hnp : (n:ℝ)<p) {K : Set (Space n)} (hK : IsCompact K)
    (h0 : (0 : Space n)∈K) {R : ℝ} (hR : 0<R) (hKR : K⊆ball 0 R) :
    ∃ G : Space n → ℝ,∃ Γ : Space n → Space n,
      Continuous G ∧ (∀ x∈K,G x=0) ∧
      (∀ x∉ball 0 R,G x=fundamentalRadialValue n (canonicalSphereArea n) p R) ∧
      MemLp Γ (ENNReal.ofReal p) volume ∧
      (∀ B : Set (Space n),Bornology.IsBounded B → SobolevPair p B G Γ) ∧
      WeakPHarmonicPair p (ball 0 R\K) G Γ ∧
      (∀ x,0≤G x ∧ G x≤fundamentalPotential n (canonicalSphereArea n) p x) ∧
      ∃ u : Space n → ℝ,∃ g : Space n → Space n,
        Continuous u ∧ (∀ x∈K,u x=1) ∧ (∀ x∉ball 0 R,u x=0) ∧ (∀ x,0≤u x ∧ u x≤1) ∧
        ZeroBoundarySobolevPair p (ball 0 R) u g ∧ SobolevPair p univ u g ∧
        BMCompactCapacityV2.relativeCapacity p K (ball 0 R)=ENNReal.ofReal (∫ x in ball 0 R,‖g x‖^p ∂volume) ∧
        (∀ x,G x=fundamentalRadialValue n (canonicalSphereArea n) p R*(1-u x)) ∧
        (∀ x,Γ x=(-fundamentalRadialValue n (canonicalSphereArea n) p R) • g x) ∧
        ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K (ball 0 R) (φ j)) ∧
          Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
          Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hn0 : 0<n := lt_of_lt_of_le (by decide : 0<2) hn
  have hn1 : 1<n := lt_of_lt_of_le (by decide : 1<2) hn
  have hnr : 1<(n:ℝ) := by exact_mod_cast hn1
  have hp : 1<p := hnr.trans hnp
  have hσ : 0<canonicalSphereArea n := canonicalSphereArea_pos hn0
  let c : ℝ := fundamentalRadialValue n (canonicalSphereArea n) p R
  let F : Space n → ℝ := fundamentalPotential n (canonicalSphereArea n) p
  have hc : 0<c := annular_radial_value_pos hnr hnp hσ hR
  have hF0 (x : Space n) : 0≤F x := annular_fundamental_nonneg hnr hnp hσ x
  have hFc : Continuous F := continuous_fundamentalPotential_supercritical n _ hnr hnp
  obtain ⟨u,g,huc,huK,huOut,hub,huW,huSob,huH,hcap,φ,hφ,hφu,hφg⟩ :=
    exists_continuous_unit_relative_capacity_potential_supercritical hn hnp hK isOpen_ball hKR isBounded_ball
  let G : Space n → ℝ := fun x=>c*(1-u x)
  let Γ : Space n → Space n := fun x=>(-c) • g x
  have hGc : Continuous G := continuous_const.mul (continuous_const.sub huc)
  have hGK (x : Space n) (hx : x∈K) : G x=0 := by simp only [G,huK x hx,sub_self,mul_zero]
  have hGout (x : Space n) (hx : x∉ball 0 R) : G x=c := by simp only [G,huOut x hx,sub_zero,mul_one]
  have hΓ : MemLp Γ (ENNReal.ofReal p) volume := by
    have hg : MemLp g (ENNReal.ofReal p) volume := by simpa only [Measure.restrict_univ] using huSob.2.2.1
    exact hg.const_smul (-c)
  have hGSob (B : Set (Space n)) (hB : Bornology.IsBounded B) : SobolevPair p B G Γ := by
    have hs := ((huSob.mono_actual (subset_univ B)).smul (-c)).add (sobolevPair_const hp hB c)
    apply hs.congr (Eventually.of_forall (fun x=>by simp only [G,Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring))
    exact Eventually.of_forall (fun x=>by simp only [Γ,Pi.add_apply,Pi.smul_apply,Pi.zero_apply,add_zero])
  have hGH : WeakPHarmonicPair p (ball 0 R\K) G Γ := by
    have hs := (huH.smul (-c)).add_const c
    apply hs.congr_ae (Eventually.of_forall (fun x=>by simp only [G,Pi.smul_apply,smul_eq_mul];ring))
    exact EventuallyEq.rfl
  have hD : IsOpen (ball (0 : Space n) R\K) := isOpen_ball.sdiff hK.isClosed
  have hDb : Bornology.IsBounded (ball (0 : Space n) R\K) := isBounded_ball.subset sdiff_subset
  have hDF : (ball (0 : Space n) R\K)⊆{x : Space n | x≠0} := by
    intro x hx hx0
    subst x
    exact hx.2 h0
  have hFH : WeakPHarmonicPair p (ball 0 R\K) F (gradient F) :=
    (weakPHarmonicPair_fundamentalPotential n hσ hnr hnp.le).mono hDF hD
  have hout (x : Space n) (hx : x∉ball 0 R) : c≤F x := by
    have hxn : R≤‖x‖ := le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hx)
    exact (fundamentalRadialValue_mono_positive n hnr hnp.le hσ hR hxn).trans_eq
      (fundamentalPotential_norm n (canonicalSphereArea n) p x)
  have hboundary : ∀ x∈frontier (ball (0 : Space n) R\K),G x≤F x := by
    intro x hx
    by_cases hxK : x∈K
    · rw [hGK x hxK]
      exact hF0 x
    · have hxn : x∉ball (0 : Space n) R := fun hxB=>(hD.frontier_eq ▸ hx).2 ⟨hxB,hxK⟩
      rw [hGout x hxn]
      exact hout x hxn
  have hboundD := hGH.leOn_of_bounded_continuous_boundary_order hn hDb hFH hGc.continuousOn hFc.continuousOn hboundary
  have hbound (x : Space n) : 0≤G x ∧ G x≤F x := by
    refine ⟨mul_nonneg hc.le (sub_nonneg.mpr (hub x).2),?_⟩
    by_cases hxK : x∈K
    · rw [hGK x hxK]
      exact hF0 x
    · by_cases hxB : x∈ball (0 : Space n) R
      · exact hboundD x ⟨hxB,hxK⟩
      · rw [hGout x hxB]
        exact hout x hxB
  exact ⟨G,Γ,hGc,hGK,hGout,hΓ,hGSob,hGH,hbound,u,g,huc,huK,huOut,hub,huW,huSob,hcap,
    (fun _=>rfl),(fun _=>rfl),φ,hφ,hφu,hφg⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_canonical_annular_green_approximant_supercritical
