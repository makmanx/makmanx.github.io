import CapacityBoundaryUniqueness

/-! Raw-data uniqueness of genuine variational capacitary potentials.
The two private closure helpers below are exact V9 dependency adaptations
from ExteriorCapacityClamp (only private names change); they add zero extra
exported proofs. Raw compact admissible approximants reconstruct actual graph
membership. No graph membership, minimizer or uniqueness premise is supplied. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE
section BoundaryClosureDependencies
variable (p q : ℝ) [Fact (1≤ENNReal.ofReal p)] [Fact (1≤ENNReal.ofReal q)]
private theorem boundary_capacityClass_of_member_mixed_limits {n : ℕ} {K : Set (Space n)}
    {w : ℕ → exteriorHomogeneousGraph p q n} (hw : ∀ j, w j ∈ exteriorCapacityClass p q K)
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : MemLp v (ENNReal.ofReal q) volume) (hh : MemLp h (ENNReal.ofReal p) volume)
    (hlu : Tendsto (fun j => eLpNorm (((w j).1.1 : Space n → ℝ)-v) (ENNReal.ofReal q) volume) atTop (𝓝 0))
    (hlg : Tendsto (fun j => eLpNorm (((w j).1.2 : Space n → Space n)-h) (ENNReal.ofReal p) volume) atTop (𝓝 0)) :
    ∃ z ∈ exteriorCapacityClass p q K,
      (z.1.1 : Space n → ℝ) =ᵐ[volume] v ∧ (z.1.2 : Space n → Space n) =ᵐ[volume] h := by
  let z0 : ExteriorScalarLp q n × ExteriorVectorLp p n := (hv.toLp v, hh.toLp h)
  have h1 : Tendsto (fun j => (w j).1.1) atTop (𝓝 z0.1) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (w j).1.1) (hv.toLp v)).mpr
    have he (j : ℕ) : eLpNorm (((w j).1.1 : Space n → ℝ)-(hv.toLp v : Space n → ℝ))
        (ENNReal.ofReal q) volume = eLpNorm (((w j).1.1 : Space n → ℝ)-v) (ENNReal.ofReal q) volume :=
      eLpNorm_congr_ae (EventuallyEq.rfl.sub (MemLp.coeFn_toLp hv))
    simpa only [he] using hlu
  have h2 : Tendsto (fun j => (w j).1.2) atTop (𝓝 z0.2) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (w j).1.2) (hh.toLp h)).mpr
    have he (j : ℕ) : eLpNorm (((w j).1.2 : Space n → Space n)-(hh.toLp h : Space n → Space n))
        (ENNReal.ofReal p) volume = eLpNorm (((w j).1.2 : Space n → Space n)-h) (ENNReal.ofReal p) volume :=
      eLpNorm_congr_ae (EventuallyEq.rfl.sub (MemLp.coeFn_toLp hh))
    simpa only [he] using hlg
  have hprod : Tendsto (fun j => (w j).1) atTop (𝓝 z0) := h1.prodMk_nhds h2
  have hz0 : z0 ∈ exteriorHomogeneousGraph p q n :=
    (isClosed_exteriorHomogeneousGraph p q n).mem_of_tendsto hprod
      (Eventually.of_forall (fun j => (w j).2))
  let z : exteriorHomogeneousGraph p q n := ⟨z0, hz0⟩
  have hsub : Tendsto w atTop (𝓝 z) := tendsto_subtype_rng.mpr hprod
  refine ⟨z, isClosed_closure.mem_of_tendsto hsub (Eventually.of_forall hw),
    MemLp.coeFn_toLp hv, MemLp.coeFn_toLp hh⟩

private theorem boundary_capacityClass_of_admissible_mixed_limits {n : ℕ} {K : Set (Space n)}
    {φ : ℕ → Space n → ℝ} (hφ : ∀ j, BMCompactCapacityV2.Admissible K univ (φ j))
    {v : Space n → ℝ} {h : Space n → Space n}
    (hv : MemLp v (ENNReal.ofReal q) volume) (hh : MemLp h (ENNReal.ofReal p) volume)
    (hlu : Tendsto (fun j => eLpNorm (φ j-v) (ENNReal.ofReal q) volume) atTop (𝓝 0))
    (hlg : Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-h x)
      (ENNReal.ofReal p) volume) atTop (𝓝 0)) :
    ∃ z ∈ exteriorCapacityClass p q K,
      (z.1.1 : Space n → ℝ) =ᵐ[volume] v ∧ (z.1.2 : Space n → Space n) =ᵐ[volume] h := by
  have hu (j : ℕ) : MemLp (φ j) (ENNReal.ofReal q) volume :=
    BMCompactCapacityV2.smooth_compactSupport_memLp (ENNReal.ofReal q) (hφ j).1 (hφ j).2.1
  have hg (j : ℕ) : MemLp (gradient (φ j)) (ENNReal.ofReal p) volume :=
    BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p) (hφ j).1 (hφ j).2.1
  let Z (j : ℕ) : ExteriorScalarLp q n × ExteriorVectorLp p n :=
    ((hu j).toLp (φ j), (hg j).toLp (gradient (φ j)))
  have hZ (j : ℕ) : Z j ∈ exteriorSmoothGraph p q n :=
    ⟨φ j, ⟨(hφ j).1, (hφ j).2.1, subset_univ _⟩, MemLp.coeFn_toLp (hu j), MemLp.coeFn_toLp (hg j)⟩
  let w (j : ℕ) : exteriorHomogeneousGraph p q n :=
    ⟨Z j, (exteriorSmoothGraph p q n).le_topologicalClosure (hZ j)⟩
  have hw (j : ℕ) : w j ∈ exteriorCapacityClass p q K :=
    subset_closure ⟨φ j, hφ j, MemLp.coeFn_toLp (hu j), MemLp.coeFn_toLp (hg j)⟩
  apply boundary_capacityClass_of_member_mixed_limits p q hw hv hh
  · have he (j : ℕ) : eLpNorm (((w j).1.1 : Space n → ℝ)-v) (ENNReal.ofReal q) volume =
        eLpNorm (φ j-v) (ENNReal.ofReal q) volume :=
      eLpNorm_congr_ae ((MemLp.coeFn_toLp (hu j)).sub EventuallyEq.rfl)
    simpa only [he] using hlu
  · have he (j : ℕ) : eLpNorm (((w j).1.2 : Space n → Space n)-h) (ENNReal.ofReal p) volume =
        eLpNorm (fun x => gradient (φ j) x-h x) (ENNReal.ofReal p) volume :=
      eLpNorm_congr_ae ((MemLp.coeFn_toLp (hg j)).sub EventuallyEq.rfl)
    simpa only [he] using hlg

end BoundaryClosureDependencies

/- Actual scalar/gradient Lp data with genuine capacity-admissible approximants
and the capacity energy are unique almost everywhere. This wire-safe statement
uses only the published scalar/PDE/capacity definitions, not an unregistered
homogeneous-graph type. -/
set_option maxHeartbeats 800000 in
theorem variational_capacity_potentials_ae_unique {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) {K : Set (Space n)} (hK : IsCompact K)
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : MemLp u (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume)
    (hg : MemLp g (ENNReal.ofReal p) volume)
    (hv : MemLp v (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume)
    (hh : MemLp h (ENNReal.ofReal p) volume)
    (hcu : BMCompactCapacityV2.relativeCapacity p K univ=ENNReal.ofReal (∫ x,‖g x‖^p ∂volume))
    (hcv : BMCompactCapacityV2.relativeCapacity p K univ=ENNReal.ofReal (∫ x,‖h x‖^p ∂volume))
    (hau : ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K univ (φ j)) ∧
      Tendsto (fun j => eLpNorm (φ j-u) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume) atTop (𝓝 0) ∧
      Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-g x) (ENNReal.ofReal p) volume) atTop (𝓝 0))
    (hav : ∃ φ : ℕ → Space n → ℝ,(∀ j,BMCompactCapacityV2.Admissible K univ (φ j)) ∧
      Tendsto (fun j => eLpNorm (φ j-v) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume) atTop (𝓝 0) ∧
      Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-h x) (ENNReal.ofReal p) volume) atTop (𝓝 0)) :
    u =ᵐ[volume] v ∧ g =ᵐ[volume] h := by
  let q : ℝ := (n : ℝ)*p/((n : ℝ)-p)
  have hpq : p≤q := by
    apply (le_div_iff₀ (sub_pos.mpr hpn)).mpr
    nlinarith [sq_nonneg p]
  haveI : Fact (1≤ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  haveI : Fact (1≤ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr (hp.le.trans hpq)⟩
  obtain ⟨φ,hφ,hlu,hlg⟩ := hau
  obtain ⟨ψ,hψ,hlv,hlh⟩ := hav
  obtain ⟨U,hU,hUu,hUg⟩ := boundary_capacityClass_of_admissible_mixed_limits p q hφ hu hg hlu hlg
  obtain ⟨V,hV,hVv,hVh⟩ := boundary_capacityClass_of_admissible_mixed_limits p q hψ hv hh hlv hlh
  obtain ⟨W,⟨hW,hWmin⟩,hUnique⟩ := existsUnique_exteriorCapacityClass_minimum p q hp hpn rfl hK
  have hWcap := capacity_eq_exteriorCapacityClass_minimum_energy p q hp hW hWmin
  have hmin (Z : exteriorHomogeneousGraph p q n) (hZ : Z∈exteriorCapacityClass p q K)
      (b : Space n → Space n) (hZb : (Z.1.2 : Space n → Space n) =ᵐ[volume] b)
      (hcb : BMCompactCapacityV2.relativeCapacity p K univ=ENNReal.ofReal (∫ x,‖b x‖^p ∂volume)) :
      ∀ z∈exteriorCapacityClass p q K,‖Z.1.2‖^p≤‖z.1.2‖^p := by
    have he : ENNReal.ofReal (‖Z.1.2‖^p)=BMCompactCapacityV2.relativeCapacity p K univ := by
      rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)]
      exact (congrArg ENNReal.ofReal (integral_congr_ae (hZb.fun_comp (fun a => ‖a‖^p)))).trans hcb.symm
    have heR := congrArg ENNReal.toReal (he.trans hWcap)
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _),
      ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] at heR
    intro z hz
    exact heR.le.trans (hWmin z hz)
  have hUW : U=W := hUnique U ⟨hU,hmin U hU g hUg hcu⟩
  have hVW : V=W := hUnique V ⟨hV,hmin V hV h hVh hcv⟩
  have hUV : U=V := hUW.trans hVW.symm
  rw [←hUV] at hVv hVh
  exact ⟨hUu.symm.trans hVv,hUg.symm.trans hVh⟩

end BMCompactPDE
#print axioms BMCompactPDE.variational_capacity_potentials_ae_unique
