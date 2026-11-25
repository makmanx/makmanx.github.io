import CriticalGreenFiniteAsymptotic
import CriticalGreenExistence
import CriticalOuterAgreement

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Pointwise Topology
namespace BMCompactPDE

/-- The real value picked out by the canonical Green capacities of all
positive closed neighbourhoods in equation 2.14. -/
def canonicalCriticalOuterCapacity {n : ℕ} (K : Set (Space n)) : ℝ :=
  sInf {c : ℝ | HasCriticalOuterCapacity (canonicalSphereArea n) K c}

private theorem canonical_capacity_of_outer_witness {n : ℕ} {K : Set (Space n)} {c : ℝ}
    (hc : HasCriticalOuterCapacity (canonicalSphereArea n) K c) :
    canonicalCriticalOuterCapacity K = c := by
  have hs : {d : ℝ | HasCriticalOuterCapacity (canonicalSphereArea n) K d} = {c} := by
    ext d
    exact ⟨fun hd=>hd.unique hc,fun hd=>by obtain rfl : d=c := hd;exact hc⟩
  rw [canonicalCriticalOuterCapacity,hs,csInf_singleton]

private theorem closed_neighborhood_critical_capacity {n : ℕ} (hn : 2≤n)
    {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty) {δ : ℝ} (hδ : 0<δ) :
    ∃ c : ℝ, HasCriticalGreenCapacity (canonicalSphereArea n) (BMCompact.closedNeighborhood δ K) c := by
  obtain ⟨G,hG,_⟩ := existsUnique_critical_exterior_green_closedNeighborhood hn hK hne hδ
  obtain ⟨k,hk,_⟩ := hG.existsUnique_finite_critical_asymptotic
  exact ⟨_,G,k,hG,hk,rfl⟩

/-- Every nonempty compact has a unique outer critical capacity through the
full positive-radius limit, with the canonical sphere-area normalization. -/
theorem existsUnique_canonical_critical_outer_capacity {n : ℕ} (hn : 2≤n)
    {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃! c : ℝ, HasCriticalOuterCapacity (canonicalSphereArea n) K c :=
  exists_criticalOuterCapacity_of_closedNeighborhood_greenCapacities
    (fun _ hδ=>closed_neighborhood_critical_capacity hn hK hne hδ)

theorem has_canonical_critical_outer_capacity {n : ℕ} (hn : 2≤n)
    {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty) :
    HasCriticalOuterCapacity (canonicalSphereArea n) K (canonicalCriticalOuterCapacity K) := by
  obtain ⟨c,hc,_⟩ := existsUnique_canonical_critical_outer_capacity hn hK hne
  rwa [canonical_capacity_of_outer_witness hc]

/-- Theorem B(a) for the actual outer value on all nonempty compacts. -/
theorem canonical_critical_outer_capacity_affine {n : ℕ} (hn : 2≤n)
    {K : Set (Space n)} (hK : IsCompact K) (hne : K.Nonempty)
    {ρ : ℝ} (hρ : 0<ρ) (a : Space n) :
    canonicalCriticalOuterCapacity (ρ • K + {a}) = ρ * canonicalCriticalOuterCapacity K :=
  canonical_capacity_of_outer_witness ((has_canonical_critical_outer_capacity hn hK hne).affine hK hρ a)

theorem canonical_critical_outer_capacity_mono {n : ℕ} (hn : 2≤n)
    {K L : Set (Space n)} (hK : IsCompact K) (hL : IsCompact L)
    (hne : K.Nonempty) (hKL : K⊆L) :
    canonicalCriticalOuterCapacity K ≤ canonicalCriticalOuterCapacity L :=
  (has_canonical_critical_outer_capacity hn hK hne).mono
    (has_canonical_critical_outer_capacity hn hL (hne.mono hKL)) hKL

/-- Theorem B(b) for any compact that admits its own normalized exterior
Green function: the outer value is exactly its original Green capacity. -/
theorem IsExteriorGreen.canonical_critical_outer_capacity_agrees
    {n : ℕ} {K : Set (Space n)} {G : Space n → ℝ}
    (hG : IsExteriorGreen n (canonicalSphereArea n) n K G) :
    ∃ k : ℝ, HasGreenAsymptotic n (canonicalSphereArea n) n G k ∧
      canonicalCriticalOuterCapacity K = greenCapacityOfConstant n (canonicalSphereArea n) n k ∧
      HasCriticalGreenCapacity (canonicalSphereArea n) K (canonicalCriticalOuterCapacity K) := by
  have hn : 1<n := by exact_mod_cast hG.1
  obtain ⟨k,hk,hout⟩ := hG.exists_asymptotic_and_criticalOuterCapacity (fun _ hδ=>
    closed_neighborhood_critical_capacity (by omega) hG.2.2.2.1 hG.2.2.2.2.1 hδ)
  have he := canonical_capacity_of_outer_witness hout
  exact ⟨k,hk,he,G,k,hG,hk,he⟩

end BMCompactPDE
#print axioms BMCompactPDE.existsUnique_canonical_critical_outer_capacity
#print axioms BMCompactPDE.has_canonical_critical_outer_capacity
#print axioms BMCompactPDE.canonical_critical_outer_capacity_affine
#print axioms BMCompactPDE.canonical_critical_outer_capacity_mono
#print axioms BMCompactPDE.IsExteriorGreen.canonical_critical_outer_capacity_agrees
