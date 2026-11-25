import ExteriorCapacityConstruction
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The first variation of the original global obstacle minimum gives exact
equilibrium flux mass and positivity on tests nonnegative on K. The closure
argument and graph coordinates adapt ExteriorCapacityConstruction. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE
variable (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]

private theorem mass_compact_smul {n : ℕ} {f : Space n → ℝ}
    (hf : HasCompactSupport f) (c : ℝ) : HasCompactSupport (c • f) :=
  hf.isCompact.of_isClosed_subset (isClosed_tsupport (c • f))
    (tsupport_smul_subset_right (fun _ : Space n => c) f)

private theorem mass_smooth_graph_node {n : ℕ} {φ : Space n → ℝ} (hφ : SmoothTest univ φ) :
    ∃ v : exteriorHomogeneousGraph p q n,
      (v.1.1 : Space n → ℝ) =ᵐ[volume] φ ∧ (v.1.2 : Space n → Space n) =ᵐ[volume] gradient φ := by
  have hφu : MemLp φ (ENNReal.ofReal q) volume :=
    BMCompactCapacityV2.smooth_compactSupport_memLp (ENNReal.ofReal q) hφ.1 hφ.2.1
  have hφg : MemLp (gradient φ) (ENNReal.ofReal p) volume :=
    BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p) hφ.1 hφ.2.1
  let z : ExteriorScalarLp q n × ExteriorVectorLp p n :=
    (hφu.toLp φ, hφg.toLp (gradient φ))
  have hz : z ∈ exteriorSmoothGraph p q n :=
    ⟨φ, ⟨hφ.1, hφ.2.1, subset_univ _⟩, MemLp.coeFn_toLp hφu, MemLp.coeFn_toLp hφg⟩
  let v : exteriorHomogeneousGraph p q n :=
    ⟨z, (exteriorSmoothGraph p q n).le_topologicalClosure hz⟩
  have hvu : (v.1.1 : Space n → ℝ) =ᵐ[volume] φ := MemLp.coeFn_toLp hφu
  have hvg : (v.1.2 : Space n → Space n) =ᵐ[volume] gradient φ := MemLp.coeFn_toLp hφg
  exact ⟨v,hvu,hvg⟩

private theorem mass_affine_obstacle {n : ℕ} {K : Set (Space n)}
    {w y : exteriorHomogeneousGraph p q n} (hw : w ∈ exteriorCapacityClass p q K)
    {ψ : Space n → ℝ} (hψ : SmoothTest univ ψ)
    (hyu : (y.1.1 : Space n → ℝ) =ᵐ[volume] ψ)
    (hyg : (y.1.2 : Space n → Space n) =ᵐ[volume] gradient ψ)
    {a t : ℝ} (ha : 0 ≤ a) (hob : ∀ x∈K, 1 ≤ a+t*ψ x) :
    a • w + t • y ∈ exteriorCapacityClass p q K := by
  have hpres : exteriorCapacitySmoothClass p q K ⊆ (fun z => a • z + t • y) ⁻¹' exteriorCapacityClass p q K := by
    rintro x ⟨φ,hφ,hxu,hxg⟩
    let f : Space n → ℝ := a • φ+t • ψ
    have hf : BMCompactCapacityV2.Admissible K univ f := by
      refine ⟨(hφ.1.const_smul a).add (hψ.1.const_smul t),
        (mass_compact_smul hφ.2.1 a).add (mass_compact_smul hψ.2.1 t),subset_univ _,?_⟩
      intro z hz
      have h := mul_le_mul_of_nonneg_left (hφ.2.2.2 z hz) ha
      change 1 ≤ a * φ z+t*ψ z
      linarith only [h,hob z hz]
    apply subset_closure
    refine ⟨f,hf,?_,?_⟩
    · filter_upwards [Lp.coeFn_add (a • x.1.1) (t • y.1.1),
        Lp.coeFn_smul a x.1.1, Lp.coeFn_smul t y.1.1, hxu, hyu]
        with z hadd hax hby hx hy
      change (((a • x.1.1+t • y.1.1 : ExteriorScalarLp q n)) : Space n → ℝ) z = f z
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hax, hby]
      simp only [f, Pi.add_apply, Pi.smul_apply, hx, hy]
    · filter_upwards [Lp.coeFn_add (a • x.1.2) (t • y.1.2),
        Lp.coeFn_smul a x.1.2, Lp.coeFn_smul t y.1.2, hxg, hyg]
        with z hadd hax hby hx hy
      change (((a • x.1.2+t • y.1.2 : ExteriorVectorLp p n)) : Space n → Space n) z = gradient f z
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hax, hby]
      simp only [Pi.smul_apply, hx, hy]
      dsimp only [f]
      rw [gradient_add_smooth_actual (f := a • φ) (h := t • ψ)
        (hφ.1.const_smul a) (hψ.1.const_smul t),
        gradient_smul_smooth_actual hφ.1 a, gradient_smul_smooth_actual hψ.1 t]
      rfl
  have hc : Continuous (fun z : exteriorHomogeneousGraph p q n => a • z+t • y) :=
    (continuous_id.const_smul a).add continuous_const
  exact (closure_minimal hpres (isClosed_closure.preimage hc)) hw

private theorem mass_derivative_graph {n : ℕ} (hp : 1<p) (w y : exteriorHomogeneousGraph p q n) :
    HasDerivAt (fun t : ℝ => ‖(w+t • y).1.2‖^p)
      (p*(∫ x, inner ℝ (pFlux p (w.1.2 x)) (y.1.2 x) ∂volume)) 0 := by
  have he (t : ℝ) : ‖(w+t • y).1.2‖^p = ∫ x, ‖w.1.2 x + t • y.1.2 x‖^p ∂volume := by
    rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add w.1.2 (t • y.1.2), Lp.coeFn_smul t y.1.2] with x h₁ h₂
    change ‖((w.1.2+t • y.1.2 : ExteriorVectorLp p n) : Space n → Space n) x‖^p = _
    rw [h₁]
    simp only [Pi.add_apply,h₂,Pi.smul_apply]
  simp_rw [he]
  exact hasDerivAt_integral_energy_line hp (Lp.memLp w.1.2) (Lp.memLp y.1.2)

/-- If a compact smooth test is one at every point of K, its equilibrium
flux pairing equals the full minimizing energy and the original capacity. -/
theorem exteriorCapacity_minimum_flux_mass {n : ℕ} (hp : 1<p)
    {K : Set (Space n)} {w : exteriorHomogeneousGraph p q n}
    (hw : w ∈ exteriorCapacityClass p q K)
    (hm : ∀ z ∈ exteriorCapacityClass p q K, ‖w.1.2‖^p ≤ ‖z.1.2‖^p)
    {η : Space n → ℝ} (hη : SmoothTest univ η) (hone : ∀ x∈K, η x=1) :
    (∫ x, inner ℝ (pFlux p (w.1.2 x)) (gradient η x) ∂volume) = (∫ x, ‖w.1.2 x‖^p ∂volume) ∧
      ENNReal.ofReal (∫ x, inner ℝ (pFlux p (w.1.2 x)) (gradient η x) ∂volume) =
        BMCompactCapacityV2.variationalCapacity p K := by
  obtain ⟨v,hvu,hvg⟩ := mass_smooth_graph_node p q hη
  let y := v-w
  let F : ℝ → ℝ := fun t => ‖(w+t • y).1.2‖^p
  have hmin : IsLocalMin F 0 := by
    filter_upwards [eventually_lt_nhds (zero_lt_one : (0:ℝ)<1)] with t ht
    have hz := mass_affine_obstacle p q hw hη hvu hvg (a:=1-t) (t:=t) (by linarith)
      (fun x hx => by rw [hone x hx]; linarith)
    have he : w+t • y = (1-t) • w+t • v := by dsimp only [y]; module
    simpa only [F,zero_smul,add_zero,he] using hm _ (he.symm ▸ hz)
  have hd := hmin.hasDerivAt_eq_zero (mass_derivative_graph p q hp w y)
  have hzero := (mul_eq_zero.mp hd).resolve_left (zero_lt_one.trans hp).ne'
  have heq : (∫ x,inner ℝ (pFlux p (w.1.2 x)) (y.1.2 x) ∂volume) =
      ∫ x, (inner ℝ (pFlux p (w.1.2 x)) (gradient η x) - ‖w.1.2 x‖^p) ∂volume := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub v.1.2 w.1.2, hvg] with x h₁ h₂
    change inner ℝ _ (((v.1.2-w.1.2 : ExteriorVectorLp p n) : Space n → Space n) x) = _
    rw [h₁,Pi.sub_apply,h₂,inner_sub_right,pFlux_inner_self hp]
  let := holderConjugate_p_dual hp
  have hFlux := memLp_pFlux hp (Lp.memLp w.1.2)
  have hI := inner_integrable_of_memLp hFlux
    (BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p) hη.1 hη.2.1)
  rw [heq,integral_sub hI (integrable_norm_rpow_of_memLp hp (Lp.memLp w.1.2))] at hzero
  have hmass := sub_eq_zero.mp hzero
  refine ⟨hmass,?_⟩
  rw [hmass,← BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)]
  exact (capacity_eq_exteriorCapacityClass_minimum_energy p q hp hw hm).symm

/-- The same actual minimizer gives a nonnegative flux functional on smooth
tests nonnegative on the compact obstacle. The sign away from K is arbitrary. -/
theorem exteriorCapacity_minimum_flux_nonneg {n : ℕ} (hp : 1<p)
    {K : Set (Space n)} {w : exteriorHomogeneousGraph p q n}
    (hw : w ∈ exteriorCapacityClass p q K)
    (hm : ∀ z ∈ exteriorCapacityClass p q K, ‖w.1.2‖^p ≤ ‖z.1.2‖^p)
    {θ : Space n → ℝ} (hθ : SmoothTest univ θ) (hpos : ∀ x∈K, 0 ≤ θ x) :
    0 ≤ ∫ x, inner ℝ (pFlux p (w.1.2 x)) (gradient θ x) ∂volume := by
  obtain ⟨v,hvu,hvg⟩ := mass_smooth_graph_node p q hθ
  let F := fun t : ℝ => ‖(w+t • v).1.2‖^p
  have hm₀ (t : ℝ) (ht : 0 ≤ t) : F 0 ≤ F t := by
    have h := mass_affine_obstacle p q hw hθ hvu hvg (a:=1) (t:=t) zero_le_one
      (fun x hx => le_add_of_nonneg_right (mul_nonneg ht (hpos x hx)))
    simpa only [F,one_smul,zero_smul,add_zero] using hm _ h
  have hd := mass_derivative_graph p q hp w v
  have hle : 0 ≤ p * (∫ x,inner ℝ (pFlux p (w.1.2 x)) (v.1.2 x) ∂volume) := by
    apply ge_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0<t)
    change 0 ≤ t⁻¹ * (F (0+t)-F 0)
    rw [zero_add]
    exact mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr (hm₀ t ht.le))
  have h := (mul_nonneg_iff_of_pos_left (zero_lt_one.trans hp)).mp hle
  exact h.trans_eq (integral_congr_ae (hvg.mono (fun x hx => congrArg (fun z => inner ℝ (pFlux p (w.1.2 x)) z) hx)))

/-- In the subcritical range the global variational problem constructs
a single minimizing field with all unit-cutoff identities and positivity
for every smooth test nonnegative on K. -/
theorem exists_subcritical_equilibrium_flux_mass {n : ℕ} (hp : 1 < p) (hpn : p < (n:ℝ))
    (hq : q = (n:ℝ)*p/((n:ℝ)-p)) {K : Set (Space n)} (hK : IsCompact K) :
    ∃ w ∈ exteriorCapacityClass p q K,
      (∀ z ∈ exteriorCapacityClass p q K, ‖w.1.2‖^p ≤ ‖z.1.2‖^p) ∧
      (∀ η, SmoothTest univ η → (∀ x∈K, η x=1) →
        (∫ x, inner ℝ (pFlux p (w.1.2 x)) (gradient η x) ∂volume) = (∫ x, ‖w.1.2 x‖^p ∂volume) ∧
        ENNReal.ofReal (∫ x, inner ℝ (pFlux p (w.1.2 x)) (gradient η x) ∂volume) =
          BMCompactCapacityV2.variationalCapacity p K) ∧
      ∀ θ, SmoothTest univ θ → (∀ x∈K, 0≤θ x) →
        0≤∫ x, inner ℝ (pFlux p (w.1.2 x)) (gradient θ x) ∂volume := by
  obtain ⟨w,hw,hm⟩ := exists_exteriorCapacityClass_minimum p q hp hpn hq hK
  exact ⟨w,hw,hm, fun _ hη hone => exteriorCapacity_minimum_flux_mass p q hp hw hm hη hone,
    fun _ hθ hpos => exteriorCapacity_minimum_flux_nonneg p q hp hw hm hθ hpos⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_subcritical_equilibrium_flux_mass
#print axioms BMCompactPDE.exteriorCapacity_minimum_flux_mass
#print axioms BMCompactPDE.exteriorCapacity_minimum_flux_nonneg
