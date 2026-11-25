import NextCriticalGlobalCondenser
import UpstreamGreenAnnularComparison
import UpstreamFundamentalSphere
import BallGreenExistence
import BallGreenOrder
import WeakHarmonicScaling

/-! Actual critical logarithmic annular Green approximants with a genuine
contained inner ball. The positive scale is F(R)-F(r0), and the global upper
barrier is ballGreen(r0), never the singular/unbounded-below raw log profile.
Geometric boundary regularity remains explicit; no capacity, candidate, trace,
bound or equation is assumed. No Green limit is asserted here. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

set_option maxHeartbeats 1400000 in
theorem exists_canonical_critical_annular_green_approximant_of_interior_balls
    {n : ℕ} (hn : 2≤n) {K : Set (Space n)} (hK : IsCompact K) {r₀ R : ℝ}
    (hr₀ : 0<r₀) (hrR : r₀<R) (hinner : closedBall (0 : Space n) r₀⊆K)
    (hKR : K⊆ball (0 : Space n) R)
    (hballs : ∀ a∈K,∃ z : Space n,∃ r : ℝ,0<r ∧ closedBall z r⊆K ∧ dist a z=r) :
    ∃ G : Space n → ℝ,∃ Γ : Space n → Space n,
      Continuous G ∧ (∀ x∈K,G x=0) ∧
      (∀ x∉ball 0 R,G x=fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) R-
        fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) r₀) ∧
      MemLp Γ (ENNReal.ofReal (n:ℝ)) volume ∧
      (∀ B : Set (Space n),Bornology.IsBounded B → SobolevPair (n:ℝ) B G Γ) ∧
      WeakPHarmonicPair (n:ℝ) (ball 0 R\K) G Γ ∧
      (∀ x,0≤G x ∧ G x≤ballGreen n (canonicalSphereArea n) (n:ℝ) r₀ x) ∧
      ∃ u : Space n → ℝ,∃ g : Space n → Space n,
        Continuous u ∧ (∀ x∈K,u x=1) ∧ (∀ x∉ball 0 R,u x=0) ∧ (∀ x,0≤u x ∧ u x≤1) ∧
        ZeroBoundarySobolevPair (n:ℝ) (ball 0 R) u g ∧ SobolevPair (n:ℝ) univ u g ∧
        BMCompactCapacityV2.relativeCapacity (n:ℝ) K (ball 0 R)=ENNReal.ofReal (∫ x in ball 0 R,‖g x‖^(n:ℝ) ∂volume) ∧
        (∀ x,G x=(fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) R-
          fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) r₀)*(1-u x)) ∧
        (∀ x,Γ x=(-(fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) R-
          fundamentalRadialValue n (canonicalSphereArea n) (n:ℝ) r₀)) • g x) ∧
        ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K (ball 0 R) (φ j)) ∧
          Tendsto (fun j=>eLpNorm (φ j-u) (ENNReal.ofReal (n:ℝ)) volume) atTop (𝓝 0) ∧
          Tendsto (fun j=>eLpNorm (fun x=>gradient (φ j) x-g x) (ENNReal.ofReal (n:ℝ)) volume) atTop (𝓝 0) := by
  let p : ℝ := (n:ℝ)
  have hn0 : 0<n := lt_of_lt_of_le (by decide : 0<2) hn
  have hnr : 1<(n:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 1<2) hn)
  have hp : 1<p := hnr
  have hσ : 0<canonicalSphereArea n := canonicalSphereArea_pos hn0
  have hR : 0<R := hr₀.trans hrR
  let c : ℝ := fundamentalRadialValue n (canonicalSphereArea n) p R-
    fundamentalRadialValue n (canonicalSphereArea n) p r₀
  let B : Space n → ℝ := ballGreen n (canonicalSphereArea n) p r₀
  have hc : 0<c := sub_pos.mpr ((strictMonoOn_fundamentalRadialValue n hnr le_rfl hσ) hr₀ hR hrR)
  have hB0 (x : Space n) : 0≤B x := ballGreen_nonneg n hnr le_rfl hσ hr₀ x
  have hBc : Continuous B := continuous_ballGreen n _ p hr₀
  obtain ⟨u,g,huc,huK,huOut,hub,huW,huSob,huH,hcap,φ,hφ,hφu,hφg⟩ :=
    exists_continuous_unit_critical_relative_capacity_potential_of_interior_tangent_balls hn hK hR hKR hballs
  have hD : IsOpen (ball (0 : Space n) R\K) := isOpen_ball.sdiff hK.isClosed
  have hDb : Bornology.IsBounded (ball (0 : Space n) R\K) := isBounded_ball.subset sdiff_subset
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
  have hDB : (ball (0 : Space n) R\K)⊆(closedBall (0 : Space n) r₀)ᶜ :=
    fun _ hx hball=>hx.2 (hinner hball)
  obtain ⟨bg,hBH0⟩ := ballGreen_isWeakPHarmonic n hσ hnr (le_refl (n:ℝ)) hr₀
  have hBH : WeakPHarmonicPair p (ball 0 R\K) B bg := hBH0.mono hDB hD
  have hout (x : Space n) (hx : x∉ball 0 R) : c≤B x := by
    have hxn : R≤‖x‖ := le_of_not_gt (by simpa only [mem_ball,dist_zero_right] using hx)
    change fundamentalRadialValue n (canonicalSphereArea n) p R-
      fundamentalRadialValue n (canonicalSphereArea n) p r₀≤ballGreen n (canonicalSphereArea n) p r₀ x
    rw [ballGreen_eq_profile_sub_of_le_norm n (canonicalSphereArea n) p r₀ (hrR.le.trans hxn)]
    exact sub_le_sub_right ((fundamentalRadialValue_mono_positive n hnr le_rfl hσ hR hxn).trans_eq
      (fundamentalPotential_norm n (canonicalSphereArea n) p x)) _
  have hboundary : ∀ x∈frontier (ball (0 : Space n) R\K),G x≤B x := by
    intro x hx
    by_cases hxK : x∈K
    · rw [hGK x hxK]
      exact hB0 x
    · have hxn : x∉ball (0 : Space n) R := fun hxB=>(hD.frontier_eq ▸ hx).2 ⟨hxB,hxK⟩
      rw [hGout x hxn]
      exact hout x hxn
  have hboundD := hGH.leOn_of_bounded_continuous_boundary_order hn hDb hBH hGc.continuousOn hBc.continuousOn hboundary
  have hbound (x : Space n) : 0≤G x ∧ G x≤B x := by
    refine ⟨mul_nonneg hc.le (sub_nonneg.mpr (hub x).2),?_⟩
    by_cases hxK : x∈K
    · rw [hGK x hxK]
      exact hB0 x
    · by_cases hxB : x∈ball (0 : Space n) R
      · exact hboundD x ⟨hxB,hxK⟩
      · rw [hGout x hxB]
        exact hout x hxB
  exact ⟨G,Γ,hGc,hGK,hGout,hΓ,hGSob,hGH,hbound,u,g,huc,huK,huOut,hub,huW,huSob,hcap,
    (fun _=>rfl),(fun _=>rfl),φ,hφ,hφu,hφg⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_canonical_critical_annular_green_approximant_of_interior_balls
