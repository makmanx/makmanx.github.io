import CriticalGreenExistence
import GreenObstacleOrder
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology ENNReal Pointwise
namespace BMCompactPDE

/-- Equation 2.19 at p=n. The outer limit takes values in [0,∞] and therefore
also covers polar compacts. Each neighborhood uses its unique actual exterior
Green function. No finite far-field constant or convergence is required. -/
theorem exists_critical_outer_green_limit {n : ℕ} (hn : 2 ≤ n) {K : Set (Space n)}
    (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ G : Ioi (0:ℝ) → Space n → ℝ, ∃ L : Space n → ℝ≥0∞,
      (∀ r, IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood r.val K) (G r)) ∧
      (∀ x, Antitone (fun r => G r x)) ∧
      (∀ x, Tendsto (fun r => ENNReal.ofReal (G r x)) atBot (𝓝 (L x))) ∧
      LowerSemicontinuous L ∧ (∀ x ∈ K, L x = 0) := by
  classical
  let R := {r : ℝ // 0 < r}
  let _ : Nonempty R := ⟨⟨(1:ℝ),(by norm_num : (0:ℝ)<1)⟩⟩
  choose G hG using fun r : R =>
    (existsUnique_critical_exterior_green_closedNeighborhood hn hK hne r.property).exists
  have hanti (x : Space n) : Antitone (fun r : R => G r x) :=
    fun r s hrs => (hG r).antitone_obstacle (hG s) (BMCompact.closedNeighborhood_mono K hrs) x
  let L : Space n → ℝ≥0∞ := fun x => ⨆ r : R, ENNReal.ofReal (G r x)
  refine ⟨G,L,hG,hanti,fun x => tendsto_atBot_iSup (fun _ _ hrs => ENNReal.ofReal_le_ofReal (hanti x hrs)),?_,?_⟩
  · exact lowerSemicontinuous_iSup fun r =>
      (ENNReal.continuous_ofReal.comp (hG r).2.2.2.2.2.1).lowerSemicontinuous
  · intro x hx
    apply le_antisymm _ (show (0:ℝ≥0∞) ≤ L x from bot_le)
    apply iSup_le
    intro r
    rw [(hG r).2.2.2.2.2.2.1 (BMCompact.subset_closedNeighborhood K r.val hx), ENNReal.ofReal_zero]

/-- Transfer the regular-neighborhood Green maximum comparison to the actual
extended-real outer Green limits for two arbitrary nonempty compacts. -/
theorem theoremC_critical_outer_of_neighborhood_comparison
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    {E F : Set (Space n)} (hE : IsCompact E) (he : E.Nonempty) (hF : IsCompact F) (hf : F.Nonempty)
    (hcomp : ∀ r : Ioi (0:ℝ), ∀ U V W : Space n → ℝ,
      IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood r.val E) U →
      IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood r.val F) V →
      IsExteriorGreen n (canonicalSphereArea n) n (t • BMCompact.closedNeighborhood r.val E +
        (1-t) • BMCompact.closedNeighborhood r.val F) W →
      ∀ y z, W (t • y + (1-t) • z) ≤ max (U y) (V z)) :
    ∃ U V W : Ioi (0:ℝ) → Space n → ℝ, ∃ u v w : Space n → ℝ≥0∞,
      (∀ r, IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood r.val E) (U r) ∧
        IsExteriorGreen n (canonicalSphereArea n) n (BMCompact.closedNeighborhood r.val F) (V r) ∧
        IsExteriorGreen n (canonicalSphereArea n) n
          (BMCompact.closedNeighborhood r.val (t • E + (1-t) • F)) (W r)) ∧
      (∀ x, Tendsto (fun r => ENNReal.ofReal (U r x)) atBot (𝓝 (u x)) ∧
        Tendsto (fun r => ENNReal.ofReal (V r x)) atBot (𝓝 (v x)) ∧
        Tendsto (fun r => ENNReal.ofReal (W r x)) atBot (𝓝 (w x))) ∧
      ∀ y z, w (t • y + (1-t) • z) ≤ max (u y) (v z) := by
  classical
  let _ : Nonempty (Ioi (0:ℝ)) := ⟨⟨(1:ℝ),(by norm_num : (0:ℝ)<1)⟩⟩
  obtain ⟨U,u,hU,_,lu,_⟩ := exists_critical_outer_green_limit hn hE he
  obtain ⟨V,v,hV,_,lv,_⟩ := exists_critical_outer_green_limit hn hF hf
  obtain ⟨W,w,hW,_,lw,_⟩ := exists_critical_outer_green_limit hn
    ((hE.smul t).add (hF.smul (1-t))) ((he.image _).add (hf.image _))
  refine ⟨U,V,W,u,v,w,fun r => ⟨hU r,hV r,hW r⟩,fun x => ⟨lu x,lv x,lw x⟩,?_⟩
  intro y z
  apply le_of_tendsto_of_tendsto' (lw _) ((lu y).max (lv z))
  intro r
  have h := hcomp r (U r) (V r) (W r) (hU r) (hV r)
  rw [BMCompact.weighted_closedNeighborhood hE hF ht ht1 r.property.le] at h
  simpa only [ENNReal.ofReal_max] using ENNReal.ofReal_le_ofReal (h (hW r) y z)

end BMCompactPDE
#print axioms BMCompactPDE.exists_critical_outer_green_limit
#print axioms BMCompactPDE.theoremC_critical_outer_of_neighborhood_comparison
