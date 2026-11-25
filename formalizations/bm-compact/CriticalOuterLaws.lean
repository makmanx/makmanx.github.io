import CriticalBallOuterCapacity
import GreenObstacleOrder
import Mathlib.Topology.Order.Monotone
import RootDilationBatch
import RadialDilation
import UpstreamGreenTranslation

/-! Critical Green and outer capacity under translations and positive scales.
The finite constant is transported with the weak PDE, and the outer radius
is reparameterized by δ/ρ. -/
noncomputable section
open Set Filter Metric Bornology
open scoped Pointwise Topology
namespace BMCompactPDE

theorem HasCriticalGreenCapacity.translate {n : ℕ} {σ c : ℝ} {K : Set (Space n)}
    (hc : HasCriticalGreenCapacity σ K c) (a : Space n) :
    HasCriticalGreenCapacity σ (K + {a}) c := by
  rcases hc with ⟨G,k,hG,hk,rfl⟩
  have he : (fun x : Space n => x + a) '' K = K + {a} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,a,rfl,rfl⟩
    · rintro ⟨y,hy,z,hz,rfl⟩
      obtain rfl : z=a := hz
      exact ⟨y,hy,rfl⟩
  have hGa := hG.translate_actual a
  rw [he] at hGa
  refine ⟨_,k,hGa,?_,rfl⟩
  change Tendsto (fun x => G x - fundamentalPotential n σ n x)
    (cobounded (Space n)) (𝓝 k) at hk
  have htail := hk.comp (tendsto_sub_const_cobounded a)
  have hshift := tendsto_fundamentalPotential_translate_sub n σ hG.1 le_rfl a
  have hadd := htail.add hshift
  rw [add_zero] at hadd
  apply hadd.congr
  intro x
  change (G (x-a)-fundamentalPotential n σ n (x-a)) +
    (fundamentalPotential n σ n (x-a)-fundamentalPotential n σ n x) =
    G (x-a)-fundamentalPotential n σ n x
  ring

theorem HasCriticalGreenCapacity.dilate {n : ℕ} {σ c ρ : ℝ} {K : Set (Space n)}
    (hc : HasCriticalGreenCapacity σ K c) (hρ : 0 < ρ) :
    HasCriticalGreenCapacity σ (ρ • K) (ρ*c) := by
  rcases hc with ⟨G,k,hG,hk,rfl⟩
  obtain ⟨hn,hp,hσ,hK,hne,hcont,hzero,⟨g,hweak⟩,_⟩ := hG
  change Tendsto (fun x => G x - fundamentalPotential n σ n x)
    (cobounded (Space n)) (𝓝 k) at hk
  let γ := σ ^ (-((n:ℝ)-1)⁻¹)
  have hγ : 0 < γ := Real.rpow_pos_of_pos hσ _
  have hpre : (fun x : Space n => ρ⁻¹ • x) ⁻¹' Kᶜ = (ρ • K)ᶜ := by
    ext x
    exact not_congr (mem_smul_set_iff_inv_smul_mem₀ hρ.ne' K x).symm
  have hd := hweak.source_zero.dilation_actual (inv_pos.mpr hρ)
  rw [mul_zero, hpre] at hd
  have hi : Tendsto (fun x : Space n => ρ⁻¹ • x) (cobounded (Space n)) (cobounded (Space n)) := by
    apply tendsto_norm_atTop_iff_cobounded.mp
    simpa only [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hρ).le] using
      ((tendsto_norm_cobounded_atTop : Tendsto (fun x : Space n => ‖x‖) _ _).const_mul_atTop (inv_pos.mpr hρ))
  have htail : HasGreenAsymptotic n σ n (fun x : Space n => G (ρ⁻¹ • x)) (k-γ*Real.log ρ) := by
    have hx : ∀ᶠ x : Space n in cobounded (Space n), x ≠ 0 := by
      filter_upwards [(tendsto_norm_cobounded_atTop : Tendsto (fun x : Space n => ‖x‖) _ _).eventually (eventually_gt_atTop 0)] with x hx
      exact norm_pos_iff.mp hx
    apply ((hk.comp hi).sub_const (γ*Real.log ρ)).congr'
    filter_upwards [hx] with x hx
    change G (ρ⁻¹ • x) - fundamentalPotential n σ n (ρ⁻¹ • x) - γ*Real.log ρ =
      G (ρ⁻¹ • x) - fundamentalPotential n σ n x
    rw [fundamentalPotential_dilate_critical n σ (inv_pos.mpr hρ) hx, Real.log_inv]
    dsimp only [γ]
    ring
  have hnew : IsExteriorGreen n σ n (ρ • K) (fun x : Space n => G (ρ⁻¹ • x)) := by
    refine ⟨hn,hp,hσ,hK.smul _,hne.smul_set,hcont.comp (continuous_const_smul _),
      ?_,⟨_,hd.harmonic_of_source_zero⟩,htail.boundedRemainder⟩
    intro x hx
    exact hzero ((mem_smul_set_iff_inv_smul_mem₀ hρ.ne' K x).mp hx)
  refine ⟨_,_,hnew,htail,?_⟩
  simp only [greenCapacityOfConstant, ite_true]
  change ρ*Real.exp (-k/γ) = Real.exp (-(k-γ*Real.log ρ)/γ)
  have ha : -(k-γ*Real.log ρ)/γ = Real.log ρ + -k/γ := by field_simp [hγ.ne'];ring
  rw [ha,Real.exp_add,Real.exp_log hρ]

/-- The translation and homogeneity identity in Theorem B(a), for any compact
set for which an outer critical capacity exists. Existence for the transformed
set is constructed from the original neighbourhood family. -/
theorem HasCriticalOuterCapacity.affine {n : ℕ} {σ c ρ : ℝ} {K : Set (Space n)}
    (hc : HasCriticalOuterCapacity σ K c) (hK : IsCompact K) (hρ : 0 < ρ) (a : Space n) :
    HasCriticalOuterCapacity σ (ρ • K + {a}) (ρ*c) := by
  rcases hc with ⟨C,hC,hlim⟩
  refine ⟨fun δ => ρ*C (δ/ρ),?_,?_⟩
  · intro δ hδ
    rw [BMCompact.affine_closedNeighborhood hK hρ hδ.le]
    exact ((hC _ (div_pos hδ hρ)).dilate hρ).translate a
  · have hd : Tendsto (fun δ : ℝ => δ/ρ) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have ht : Tendsto (fun δ : ℝ => δ/ρ) (𝓝[>] (0:ℝ)) (𝓝 ((0:ℝ)/ρ)) :=
          ((continuous_id.div_const ρ).continuousAt (x := 0)).continuousWithinAt.tendsto
        simpa only [zero_div] using ht
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact div_pos hδ hρ
    exact (hlim.comp hd).const_mul ρ


theorem HasCriticalGreenCapacity.pos {n : ℕ} {σ c : ℝ} {K : Set (Space n)}
    (hc : HasCriticalGreenCapacity σ K c) : 0 < c := by
  rcases hc with ⟨_,k,_,_,rfl⟩
  simpa [greenCapacityOfConstant] using Real.exp_pos (-k / σ ^ (-((n:ℝ)-1)⁻¹))

theorem HasCriticalGreenCapacity.mono {n : ℕ} {σ c d : ℝ} {K L : Set (Space n)}
    (hc : HasCriticalGreenCapacity σ K c) (hd : HasCriticalGreenCapacity σ L d)
    (hKL : K ⊆ L) : c ≤ d := by
  rcases hc with ⟨G,k,hG,hk,rfl⟩
  rcases hd with ⟨H,l,hH,hl,rfl⟩
  have hle := hG.asymptotic_constant_antitone_obstacle hH hKL hk hl
  simp only [greenCapacityOfConstant, ite_true]
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (neg_le_neg hle) (Real.rpow_nonneg hG.2.2.1.le _)

theorem HasCriticalOuterCapacity.mono {n : ℕ} {σ c d : ℝ} {K L : Set (Space n)}
    (hc : HasCriticalOuterCapacity σ K c) (hd : HasCriticalOuterCapacity σ L d)
    (hKL : K ⊆ L) : c ≤ d := by
  rcases hc with ⟨C,hC,hc⟩
  rcases hd with ⟨D,hD,hd⟩
  apply le_of_tendsto_of_tendsto hc hd
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hC δ hδ).mono (hD δ hδ) (cthickening_subset_of_subset δ hKL)

theorem exists_criticalOuterCapacity_of_closedNeighborhood_greenCapacities
    {n : ℕ} {σ : ℝ} {K : Set (Space n)}
    (hneigh : ∀ δ : ℝ, 0 < δ →
      ∃ c, HasCriticalGreenCapacity σ (BMCompact.closedNeighborhood δ K) c) :
    ∃! c, HasCriticalOuterCapacity σ K c := by
  classical
  let C : ℝ → ℝ := fun δ => if hp : 0 < δ then (hneigh δ hp).choose else 0
  have hC (δ : ℝ) (hδ : 0 < δ) :
      HasCriticalGreenCapacity σ (BMCompact.closedNeighborhood δ K) (C δ) := by
    simpa only [C,dif_pos hδ] using (hneigh δ hδ).choose_spec
  have hmono : MonotoneOn C (Ioi (0:ℝ)) := by
    intro δ hδ ε hε hle
    exact (hC δ hδ).mono (hC ε hε) (BMCompact.closedNeighborhood_mono K hle)
  have hb : BddBelow (C '' Ioi (0:ℝ)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨δ,hδ,rfl⟩
    exact (hC δ hδ).pos.le
  have hc : HasCriticalOuterCapacity σ K (sInf (C '' Ioi (0:ℝ))) :=
    ⟨C,hC,hmono.tendsto_nhdsGT hb⟩
  exact ⟨_, hc, fun _ hd => hd.unique hc⟩

end BMCompactPDE
#print axioms BMCompactPDE.HasCriticalGreenCapacity.translate
#print axioms BMCompactPDE.HasCriticalGreenCapacity.dilate
#print axioms BMCompactPDE.HasCriticalOuterCapacity.affine
#print axioms BMCompactPDE.HasCriticalGreenCapacity.pos
#print axioms BMCompactPDE.HasCriticalGreenCapacity.mono
#print axioms BMCompactPDE.HasCriticalOuterCapacity.mono
#print axioms BMCompactPDE.exists_criticalOuterCapacity_of_closedNeighborhood_greenCapacities
