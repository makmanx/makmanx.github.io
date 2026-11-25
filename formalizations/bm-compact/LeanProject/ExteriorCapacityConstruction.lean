import ExteriorCapacityBridge
import RootAllpPoincare
import ExteriorGlobalConstruction

/-! Exact bounded-condenser and compact-capacity construction batch; readable segments add zero extra counts. -/
section ExteriorSegment_ExteriorAllpCondenser

/-! The bounded condenser construction extends to every p>1, n>=2 using
the genuine all-p bounded-domain Poincare inverse. The proof below adapts the
immutable ExteriorPlateauMin minimum body (SHA256 78144c63aaf50dba1799cf8a1ffc5b2f6de7f8f4f01b34551462b88a7cf49e12) solely by replacing
its subcritical inverse bound with the proved all-p inverse. This broadens
bounded condensers; it asserts no p>=n exterior Green behavior at infinity. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)

set_option maxHeartbeats 1000000 in
theorem exists_exteriorPlateauClass_minimum_allp {n : ℕ} (hn : 2 ≤ n)
    {U O : Set (Space n)} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hUc : IsCompact (closure U)) (hUO : closure U ⊆ O) :
    ∃ v ∈ exteriorPlateauClass p hp U O,
      ∀ z ∈ exteriorPlateauClass p hp U O, ‖v.1.2‖^p ≤ ‖z.1.2‖^p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  letI : CompleteSpace (w0LpGraph p hp n O) :=
    (isClosed_w0LpGraph p hp n O).completeSpace_coe
  let J : w0LpGraph p hp n O → ℝ := fun w => ‖w.1.2‖^p
  obtain ⟨A, hA⟩ := exists_w0LpGradient_antilipschitz_allp p hp hn hOb
  let C : ℝ := (A : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hinv (w : w0LpGraph p hp n O) : ‖w‖ ≤ C*‖w.1.2‖ := by
    have hh : ‖w‖ ≤ (A : ℝ)*‖w.1.2‖ := by
      simpa only [dist_eq_norm, map_zero, sub_zero, w0LpGradient_apply] using hA.le_mul_dist w 0
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _))
  have hcont : Continuous J :=
    (w0LpGradient p hp n O).continuous.norm.rpow_const (fun _ => Or.inr hp0.le)
  have hbdd : BddBelow (J '' exteriorPlateauClass p hp U O) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hcoercive : ∀ a : ℝ, ∃ R : ℝ,
      ∀ w ∈ exteriorPlateauClass p hp U O, J w ≤ a → ‖w‖ ≤ R := by
    intro a
    refine ⟨C*(a+1), ?_⟩
    intro w _ hw
    have hpow : ‖w.1.2‖ ≤ ‖w.1.2‖^p + 1 := by
      by_cases ht : ‖w.1.2‖ ≤ 1
      · linarith [Real.rpow_nonneg (norm_nonneg w.1.2) p]
      · have hh := Real.self_le_rpow_of_one_le (le_of_not_ge ht) hp.le
        linarith
    exact (hinv w).trans (mul_le_mul_of_nonneg_left (by dsimp [J] at hw; linarith) hC.le)
  have hgap : ∀ R ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧
      ∀ x ∈ exteriorPlateauClass p hp U O, ∀ y ∈ exteriorPlateauClass p hp U O,
        ‖x‖ ≤ R → ‖y‖ ≤ R → ε ≤ ‖x-y‖ →
        J ((1/2 : ℝ) • x + (1/2 : ℝ) • y) ≤ (J x+J y)/2-κ := by
    intro R ε hε
    obtain ⟨κ, hκ, hfield⟩ := BMCompactBanach.lp_bounded_midpoint_gap
      (E := Space n) (μ := volume.restrict O) hp R (ε/C) (div_pos hε hC)
    refine ⟨κ, hκ, ?_⟩
    intro x _ y _ hx hy hxy
    have ha : ‖x-y‖ ≤ (A : ℝ)*‖x.1.2-y.1.2‖ := by
      simpa only [dist_eq_norm, w0LpGradient_apply] using hA.le_mul_dist x y
    have he : ε ≤ C*‖x.1.2-y.1.2‖ :=
      hxy.trans (ha.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)))
    have hsep : ε/C ≤ ‖x.1.2-y.1.2‖ :=
      (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using he)
    have hFx : ‖x.1.2‖ ≤ R := (le_max_right ‖x.1.1‖ ‖x.1.2‖).trans hx
    have hFy : ‖y.1.2‖ ≤ R := (le_max_right ‖y.1.1‖ ‖y.1.2‖).trans hy
    have hh := hfield x.1.2 y.1.2 hFx hFy hsep
    have hm : ((1/2 : ℝ) • x + (1/2 : ℝ) • y).1.2 =
        (1/2 : ℝ) • (x.1.2+y.1.2) := by
      change (1/2 : ℝ) • x.1.2 + (1/2 : ℝ) • y.1.2 = _
      rw [smul_add]
    dsimp only [J]
    rw [hm]
    linarith
  exact BMCompactBanach.exists_minimum_of_coercive_bounded_midpoint_gap
    (exteriorPlateauClass_nonempty p hp hO hUc hUO)
    (isClosed_exteriorPlateauClass p hp U O) (convex_exteriorPlateauClass p hp U O)
    hcont.continuousOn hbdd hcoercive hgap

/-- A genuine bounded Sobolev condenser minimum with an inner plateau.
Neither an admissible weak minimizer nor compactness/existence is assumed. -/
theorem exists_bounded_plateau_energy_minimum_allp {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hn : 2 ≤ n) {U O : Set (Space n)}
    (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hUc : IsCompact (closure U)) (hUO : closure U ⊆ O) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      ZeroBoundarySobolevPair p O u g ∧
      (∀ᵐ x ∂volume.restrict O, x ∈ U → u x = 1) ∧
      ∀ (v : Space n → ℝ) (h : Space n → Space n),
        ZeroBoundarySobolevPair p O v h →
        (∀ᵐ x ∂volume.restrict O, x ∈ U → v x = 1) →
        (∫ x in O, ‖g x‖^p) ≤ ∫ x in O, ‖h x‖^p := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨w, hw, hmin⟩ := exists_exteriorPlateauClass_minimum_allp p hp hn hO hOb hUc hUO
  refine ⟨w.1.1, w.1.2, w.2, hw, ?_⟩
  intro v h hv hvU
  obtain ⟨z, hzu, hzg⟩ := hv.exists_w0LpGraph_representatives hp
  have hz : z ∈ exteriorPlateauClass p hp U O := by
    filter_upwards [hzu, hvU] with x hx hy
    intro hxU
    exact hx.trans (hy hxU)
  have hh := hmin z hz
  rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp),
    BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)] at hh
  have he : (∫ x in O, ‖(z.1.2 : Space n → Space n) x‖^p) =
      ∫ x in O, ‖h x‖^p := integral_congr_ae (hzg.fun_comp (fun a => ‖a‖^p))
  exact hh.trans_eq he


theorem exists_bounded_plateau_harmonic_minimum_allp {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hn : 2 ≤ n) {U O : Set (Space n)}
    (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hUc : IsCompact (closure U)) (hUO : closure U ⊆ O) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      ZeroBoundarySobolevPair p O u g ∧
      (∀ᵐ x ∂volume.restrict O, x ∈ U → u x = 1) ∧
      WeakPHarmonicPair p (O \ closure U) u g ∧
      ∀ (v : Space n → ℝ) (h : Space n → Space n),
        ZeroBoundarySobolevPair p O v h →
        (∀ᵐ x ∂volume.restrict O, x ∈ U → v x = 1) →
        (∫ x in O, ‖g x‖^p) ≤ ∫ x in O, ‖h x‖^p := by
  obtain ⟨u, g, hu, huU, hm⟩ := exists_bounded_plateau_energy_minimum_allp hp hn hO hOb hUc hUO
  exact ⟨u, g, hu, huU, plateau_minimum_weakPHarmonic_off_closure hO hu huU hm, hm⟩

/-- A constructed all-p bounded weak condenser with a true compact-capacity
lower bound on its energy. The capacity set sits inside an OPEN plateau. -/
theorem exists_bounded_condenser_capacity_bound_allp {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hn : 2 ≤ n) {K U O : Set (Space n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hUc : IsCompact (closure U)) (hUO : closure U ⊆ O) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      ZeroBoundarySobolevPair p O u g ∧
      (∀ᵐ x ∂volume.restrict O, x ∈ U → u x = 1) ∧
      WeakPHarmonicPair p (O \ closure U) u g ∧
      BMCompactCapacityV2.relativeCapacity p K O ≤ ENNReal.ofReal (∫ x in O, ‖g x‖^p) := by
  obtain ⟨u, g, hu, huU, he, -⟩ :=
    exists_bounded_plateau_harmonic_minimum_allp hp hn hO hOb hUc hUO
  exact ⟨u, g, hu, huU, he,
    relativeCapacity_le_plateau_energy hK hU hKU (subset_closure.trans hUO) hOb hu huU⟩

end BMCompactPDE

end -- original noncomputable section
end ExteriorSegment_ExteriorAllpCondenser

section ExteriorSegment_ExteriorCapacityMinimum

/-! Genuine variational capacity attainment in the concrete function-valued
homogeneous graph. The admissible class is the norm closure of actual smooth
compact test pairs whose scalar is >=1 on the actual compact K. This retains
the capacity's genuine obstacle approximation, including for thin sets; it
never replaces it by an a.e. condition on K. No potential or compactness premise
is supplied. Selected pointwise traces and manuscript normalization remain
separate unproved assertions. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal ContDiff
namespace BMCompactPDE

variable (p q : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]

set_option maxHeartbeats 1000000 in
theorem exists_exteriorHomogeneousEnergy_minimum {n : ℕ}
    (hp : 1 < p) (hpn : p < (n : ℝ)) (hq : q = (n : ℝ)*p/((n : ℝ)-p))
    {T : Set (exteriorHomogeneousGraph p q n)} (hne : T.Nonempty)
    (hclosed : IsClosed T) (hconv : Convex ℝ T) :
    ∃ w ∈ T, ∀ z ∈ T, ‖w.1.2‖^p ≤ ‖z.1.2‖^p := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  letI : CompleteSpace (exteriorHomogeneousGraph p q n) :=
    (isClosed_exteriorHomogeneousGraph p q n).completeSpace_coe
  let J : exteriorHomogeneousGraph p q n → ℝ := fun w => ‖w.1.2‖^p
  obtain ⟨A, hA⟩ := exists_exteriorHomogeneousGradient_antilipschitz p q hp hpn hq
  have hproj (w : exteriorHomogeneousGraph p q n) :
      exteriorHomogeneousGradient p q n w = w.1.2 := rfl
  have hproj0 : (0 : exteriorHomogeneousGraph p q n).1.2 =
      (0 : ExteriorVectorLp p n) := rfl
  let C : ℝ := (A : ℝ)+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hinv (w : exteriorHomogeneousGraph p q n) : ‖w‖ ≤ C*‖w.1.2‖ := by
    have hh : ‖w‖ ≤ (A : ℝ)*‖w.1.2‖ := by
      simpa only [dist_eq_norm, hproj, hproj0, sub_zero] using hA.le_mul_dist w 0
    exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _))
  have hcont : Continuous J :=
    (exteriorHomogeneousGradient p q n).continuous.norm.rpow_const (fun _ => Or.inr hp0.le)
  have hbdd : BddBelow (J '' T) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hcoercive : ∀ a : ℝ, ∃ R : ℝ,
      ∀ w ∈ T, J w ≤ a → ‖w‖ ≤ R := by
    intro a
    refine ⟨C*(a+1), ?_⟩
    intro w _ hw
    have hpow : ‖w.1.2‖ ≤ ‖w.1.2‖^p+1 := by
      by_cases ht : ‖w.1.2‖ ≤ 1
      · linarith [Real.rpow_nonneg (norm_nonneg w.1.2) p]
      · have hh := Real.self_le_rpow_of_one_le (le_of_not_ge ht) hp.le
        linarith
    exact (hinv w).trans (mul_le_mul_of_nonneg_left (by dsimp [J] at hw; linarith) hC.le)
  have hgap : ∀ R ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧
      ∀ x ∈ T, ∀ y ∈ T,
        ‖x‖ ≤ R → ‖y‖ ≤ R → ε ≤ ‖x-y‖ →
        J ((1/2 : ℝ) • x+(1/2 : ℝ) • y) ≤ (J x+J y)/2-κ := by
    intro R ε hε
    obtain ⟨κ, hκ, hfield⟩ := BMCompactBanach.lp_bounded_midpoint_gap
      (E := Space n) (μ := (volume : Measure (Space n))) hp R (ε/C) (div_pos hε hC)
    refine ⟨κ, hκ, ?_⟩
    intro x _ y _ hx hy hxy
    have ha : ‖x-y‖ ≤ (A : ℝ)*‖x.1.2-y.1.2‖ := by
      simpa only [dist_eq_norm, hproj] using hA.le_mul_dist x y
    have he : ε ≤ C*‖x.1.2-y.1.2‖ :=
      hxy.trans (ha.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _)))
    have hsep : ε/C ≤ ‖x.1.2-y.1.2‖ :=
      (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using he)
    have hFx : ‖x.1.2‖ ≤ R := (le_max_right ‖x.1.1‖ ‖x.1.2‖).trans hx
    have hFy : ‖y.1.2‖ ≤ R := (le_max_right ‖y.1.1‖ ‖y.1.2‖).trans hy
    have hh := hfield x.1.2 y.1.2 hFx hFy hsep
    have hm : ((1/2 : ℝ) • x+(1/2 : ℝ) • y).1.2 =
        (1/2 : ℝ) • (x.1.2+y.1.2) := by
      change (1/2 : ℝ) • x.1.2+(1/2 : ℝ) • y.1.2 = _
      rw [smul_add]
    dsimp only [J]
    rw [hm]
    linarith
  exact BMCompactBanach.exists_minimum_of_coercive_bounded_midpoint_gap
    hne
    hclosed hconv
    hcont.continuousOn hbdd hcoercive hgap


def exteriorCapacitySmoothClass {n : ℕ} (K : Set (Space n)) :
    Set (exteriorHomogeneousGraph p q n) :=
  {w | ∃ φ : Space n → ℝ, BMCompactCapacityV2.Admissible K univ φ ∧
    (w.1.1 : Space n → ℝ) =ᵐ[volume] φ ∧
    (w.1.2 : Space n → Space n) =ᵐ[volume] gradient φ}

def exteriorCapacityClass {n : ℕ} (K : Set (Space n)) :
    Set (exteriorHomogeneousGraph p q n) := closure (exteriorCapacitySmoothClass p q K)

private theorem exterior_hasCompactSupport_const_smul {n : ℕ} {f : Space n → ℝ}
    (hf : HasCompactSupport f) (c : ℝ) : HasCompactSupport (c • f) :=
  hf.isCompact.of_isClosed_subset (isClosed_tsupport (c • f))
    (tsupport_smul_subset_right (fun _ : Space n => c) f)

theorem convex_exteriorCapacityClass {n : ℕ} (K : Set (Space n)) :
    Convex ℝ (exteriorCapacityClass p q K) := by
  have hs : Convex ℝ (exteriorCapacitySmoothClass p q K) := by
    intro x hx y hy a b ha hb hab
    obtain ⟨φ, hφ, hxu, hxg⟩ := hx
    obtain ⟨ψ, hψ, hyu, hyg⟩ := hy
    let f : Space n → ℝ := a • φ+b • ψ
    have hf : BMCompactCapacityV2.Admissible K univ f := by
      refine ⟨(hφ.1.const_smul a).add (hψ.1.const_smul b),
        (exterior_hasCompactSupport_const_smul hφ.2.1 a).add
          (exterior_hasCompactSupport_const_smul hψ.2.1 b), subset_univ _, ?_⟩
      intro z hz
      have hh := add_le_add (mul_le_mul_of_nonneg_left (hφ.2.2.2 z hz) ha)
        (mul_le_mul_of_nonneg_left (hψ.2.2.2 z hz) hb)
      simpa only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, hab] using hh
    refine ⟨f, hf, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_add (a • x.1.1) (b • y.1.1),
        Lp.coeFn_smul a x.1.1, Lp.coeFn_smul b y.1.1, hxu, hyu]
        with z hadd hax hby hx hy
      change (((a • x.1.1+b • y.1.1 : ExteriorScalarLp q n)) : Space n → ℝ) z = f z
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hax, hby]
      simp only [f, Pi.add_apply, Pi.smul_apply, hx, hy]
    · filter_upwards [Lp.coeFn_add (a • x.1.2) (b • y.1.2),
        Lp.coeFn_smul a x.1.2, Lp.coeFn_smul b y.1.2, hxg, hyg]
        with z hadd hax hby hx hy
      change (((a • x.1.2+b • y.1.2 : ExteriorVectorLp p n)) : Space n → Space n) z = gradient f z
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hax, hby]
      simp only [Pi.smul_apply, hx, hy]
      dsimp only [f]
      rw [gradient_add_smooth_actual (f := a • φ) (h := b • ψ)
        (hφ.1.const_smul a) (hψ.1.const_smul b),
        gradient_smul_smooth_actual hφ.1 a, gradient_smul_smooth_actual hψ.1 b]
      rfl
  exact hs.closure

theorem exteriorCapacityClass_nonempty {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) : (exteriorCapacityClass p q K).Nonempty := by
  obtain ⟨φ, hφ⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK isOpen_univ (subset_univ _)
  have hu : MemLp φ (ENNReal.ofReal q) volume :=
    BMCompactCapacityV2.smooth_compactSupport_memLp (ENNReal.ofReal q) hφ.1 hφ.2.1
  have hg : MemLp (gradient φ) (ENNReal.ofReal p) volume :=
    BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p) hφ.1 hφ.2.1
  let z : ExteriorScalarLp q n × ExteriorVectorLp p n := (hu.toLp φ, hg.toLp (gradient φ))
  have hz : z ∈ exteriorSmoothGraph p q n :=
    ⟨φ, ⟨hφ.1, hφ.2.1, subset_univ _⟩, MemLp.coeFn_toLp hu, MemLp.coeFn_toLp hg⟩
  let w : exteriorHomogeneousGraph p q n :=
    ⟨z, (exteriorSmoothGraph p q n).le_topologicalClosure hz⟩
  refine ⟨w, subset_closure ?_⟩
  exact ⟨φ, hφ, MemLp.coeFn_toLp hu, MemLp.coeFn_toLp hg⟩

theorem exteriorCapacityClass_smooth_approximation {n : ℕ} {K : Set (Space n)}
    {w : exteriorHomogeneousGraph p q n} (hw : w ∈ exteriorCapacityClass p q K) :
    ∃ φ : ℕ → Space n → ℝ, (∀ j, BMCompactCapacityV2.Admissible K univ (φ j)) ∧
      Tendsto (fun j => eLpNorm (φ j-(w.1.1 : Space n → ℝ)) (ENNReal.ofReal q) volume)
        atTop (𝓝 0) ∧
      Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-(w.1.2 : Space n → Space n) x)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  obtain ⟨z, hz, hl⟩ := mem_closure_iff_seq_limit.mp hw
  choose φ hφ hzu hzg using hz
  have h1 := (continuous_fst.tendsto w.1).comp ((continuous_subtype_val.tendsto w).comp hl)
  have h2 := (continuous_snd.tendsto w.1).comp ((continuous_subtype_val.tendsto w).comp hl)
  have hl1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (z j).1.1) w.1.1).mp h1
  have hl2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (z j).1.2) w.1.2).mp h2
  refine ⟨φ, hφ, ?_, ?_⟩
  · have he (j : ℕ) : eLpNorm (φ j-(w.1.1 : Space n → ℝ)) (ENNReal.ofReal q) volume =
        eLpNorm (((z j).1.1 : Space n → ℝ)-(w.1.1 : Space n → ℝ)) (ENNReal.ofReal q) volume :=
      eLpNorm_congr_ae ((hzu j).symm.sub EventuallyEq.rfl)
    simpa only [he] using hl1
  · have he (j : ℕ) : eLpNorm (fun x => gradient (φ j) x-(w.1.2 : Space n → Space n) x)
        (ENNReal.ofReal p) volume =
        eLpNorm (((z j).1.2 : Space n → Space n)-(w.1.2 : Space n → Space n)) (ENNReal.ofReal p) volume :=
      eLpNorm_congr_ae ((hzg j).symm.sub EventuallyEq.rfl)
    simpa only [he] using hl2

theorem exists_exteriorCapacityClass_minimum {n : ℕ}
    (hp : 1 < p) (hpn : p < (n : ℝ)) (hq : q = (n : ℝ)*p/((n : ℝ)-p))
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ w ∈ exteriorCapacityClass p q K,
      ∀ z ∈ exteriorCapacityClass p q K, ‖w.1.2‖^p ≤ ‖z.1.2‖^p := by
  exact exists_exteriorHomogeneousEnergy_minimum p q hp hpn hq
    (exteriorCapacityClass_nonempty p q hK) isClosed_closure (convex_exteriorCapacityClass p q K)

/-- Equality with the actual smooth-test infimum, derived from actual strong
closure and actual minimization; no capacity identification is assumed. -/
theorem capacity_eq_exteriorCapacityClass_minimum_energy {n : ℕ} (hp : 1 < p)
    {K : Set (Space n)} {w : exteriorHomogeneousGraph p q n}
    (hw : w ∈ exteriorCapacityClass p q K)
    (hm : ∀ z ∈ exteriorCapacityClass p q K, ‖w.1.2‖^p ≤ ‖z.1.2‖^p) :
    BMCompactCapacityV2.relativeCapacity p K univ = ENNReal.ofReal (‖w.1.2‖^p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  let J : exteriorHomogeneousGraph p q n → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z.1.2‖^p)
  have hJ : Continuous J := ENNReal.continuous_ofReal.comp
    ((exteriorHomogeneousGradient p q n).continuous.norm.rpow_const (fun _ => Or.inr hp0.le))
  have hE (z : exteriorHomogeneousGraph p q n) (φ : Space n → ℝ)
      (hφ : BMCompactCapacityV2.Admissible K univ φ)
      (hzg : (z.1.2 : Space n → Space n) =ᵐ[volume] gradient φ) :
      BMCompactCapacityV2.pEnergy p univ φ = J z := by
    rw [BMCompactCapacityV2.pEnergy_univ_eq_ofReal_integral p hp0 hφ.1 hφ.2.1]
    change ENNReal.ofReal (∫ x, ‖gradient φ x‖^p ∂volume) = ENNReal.ofReal (‖z.1.2‖^p)
    congr 1
    rw [BMCompactNonlinear.lp_norm_rpow_eq_integral hp0]
    exact (integral_congr_ae (hzg.fun_comp (fun a => ‖a‖^p))).symm
  apply le_antisymm
  · have hs : exteriorCapacitySmoothClass p q K ⊆
        {z | BMCompactCapacityV2.relativeCapacity p K univ ≤ J z} := by
      rintro z ⟨φ, hφ, _, hzg⟩
      exact (BMCompactCapacityV2.relativeCapacity_le_energy p hφ).trans_eq (hE z φ hφ hzg)
    exact (closure_minimal hs (isClosed_le continuous_const hJ)) hw
  · unfold BMCompactCapacityV2.relativeCapacity
    apply le_iInf
    intro φ
    apply le_iInf
    intro hφ
    have hu : MemLp φ (ENNReal.ofReal q) volume :=
      BMCompactCapacityV2.smooth_compactSupport_memLp (ENNReal.ofReal q) hφ.1 hφ.2.1
    have hg : MemLp (gradient φ) (ENNReal.ofReal p) volume :=
      BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p) hφ.1 hφ.2.1
    let z : ExteriorScalarLp q n × ExteriorVectorLp p n := (hu.toLp φ, hg.toLp (gradient φ))
    have hz : z ∈ exteriorSmoothGraph p q n :=
      ⟨φ, ⟨hφ.1, hφ.2.1, subset_univ _⟩, MemLp.coeFn_toLp hu, MemLp.coeFn_toLp hg⟩
    let v : exteriorHomogeneousGraph p q n :=
      ⟨z, (exteriorSmoothGraph p q n).le_topologicalClosure hz⟩
    have hv : v ∈ exteriorCapacityClass p q K :=
      subset_closure ⟨φ, hφ, MemLp.coeFn_toLp hu, MemLp.coeFn_toLp hg⟩
    exact (ENNReal.ofReal_le_ofReal (hm v hv)).trans_eq (hE v φ hφ (MemLp.coeFn_toLp hg)).symm

private theorem exteriorCapacityClass_add_smooth_off {n : ℕ} {K : Set (Space n)}
    {w v : exteriorHomogeneousGraph p q n} (hw : w ∈ exteriorCapacityClass p q K)
    {φ : Space n → ℝ} (hφ : SmoothTest Kᶜ φ)
    (hvu : (v.1.1 : Space n → ℝ) =ᵐ[volume] φ)
    (hvg : (v.1.2 : Space n → Space n) =ᵐ[volume] gradient φ) (t : ℝ) :
    w+t • v ∈ exteriorCapacityClass p q K := by
  have hφ0 (x : Space n) (hx : x ∈ K) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => (hφ.2.2 ht) hx)
  have hpres : exteriorCapacitySmoothClass p q K ⊆
      (fun z => z+t • v) ⁻¹' exteriorCapacityClass p q K := by
    rintro z ⟨ψ, hψ, hzu, hzg⟩
    have hf : BMCompactCapacityV2.Admissible K univ (ψ+t • φ) := by
      refine ⟨hψ.1.add (hφ.1.const_smul t), hψ.2.1.add (exterior_hasCompactSupport_const_smul hφ.2.1 t),
        subset_univ _, ?_⟩
      intro x hx
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hφ0 x hx,
        mul_zero, add_zero] using hψ.2.2.2 x hx
    apply subset_closure
    refine ⟨ψ+t • φ, hf, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_add z.1.1 (t • v.1.1), Lp.coeFn_smul t v.1.1, hzu, hvu]
        with x ha hs hz hv
      change ((z.1.1+t • v.1.1 : ExteriorScalarLp q n) : Space n → ℝ) x = _
      rw [ha]
      simp only [Pi.add_apply]
      rw [hs]
      simp only [Pi.add_apply, Pi.smul_apply, hz, hv]
    · filter_upwards [Lp.coeFn_add z.1.2 (t • v.1.2), Lp.coeFn_smul t v.1.2, hzg, hvg]
        with x ha hs hz hv
      change ((z.1.2+t • v.1.2 : ExteriorVectorLp p n) : Space n → Space n) x = _
      rw [ha]
      simp only [Pi.add_apply]
      rw [hs]
      simp only [Pi.smul_apply, hz, hv]
      rw [gradient_add_smooth_actual (f := ψ) (h := t • φ) hψ.1 (hφ.1.const_smul t), gradient_smul_smooth_actual hφ.1 t]
      rfl
  have hc : Continuous (fun z : exteriorHomogeneousGraph p q n => z+t • v) :=
    continuous_id.add continuous_const
  exact (closure_minimal hpres (isClosed_closure.preimage hc)) hw

set_option maxHeartbeats 1000000 in
private theorem exteriorCapacityClass_minimum_smooth_equation {n : ℕ} (hp : 1 < p)
    {K : Set (Space n)} (w : exteriorHomogeneousGraph p q n)
    (hw : w ∈ exteriorCapacityClass p q K)
    (hm : ∀ z ∈ exteriorCapacityClass p q K, ‖w.1.2‖^p ≤ ‖z.1.2‖^p)
    {φ : Space n → ℝ} (hφ : SmoothTest Kᶜ φ) :
    (∫ x, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume) = 0 := by
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
  have hwu (t : ℝ) : ((w+t • v).1.1 : Space n → ℝ) =ᵐ[volume]
      (fun x => (w.1.1 : Space n → ℝ) x+t • φ x) := by
    filter_upwards [Lp.coeFn_add w.1.1 (t • v.1.1), Lp.coeFn_smul t v.1.1, hvu]
      with x ha hs hv
    change ((w.1.1+t • v.1.1 : ExteriorScalarLp q n) : Space n → ℝ) x = _
    rw [ha]
    simp only [Pi.add_apply]
    rw [hs]
    simp only [Pi.smul_apply, hv]
  have hwg (t : ℝ) : ((w+t • v).1.2 : Space n → Space n) =ᵐ[volume]
      (fun x => (w.1.2 : Space n → Space n) x+t • gradient φ x) := by
    filter_upwards [Lp.coeFn_add w.1.2 (t • v.1.2), Lp.coeFn_smul t v.1.2, hvg]
      with x ha hs hv
    change ((w.1.2+t • v.1.2 : ExteriorVectorLp p n) : Space n → Space n) x = _
    rw [ha]
    simp only [Pi.add_apply]
    rw [hs]
    simp only [Pi.smul_apply, hv]
  have ht (t : ℝ) : w+t • v ∈ exteriorCapacityClass p q K :=
    exteriorCapacityClass_add_smooth_off p q hw hφ hvu hvg t
  let F : ℝ → ℝ := fun t => ∫ x, ‖(w.1.2 : Space n → Space n) x+t • gradient φ x‖^p ∂volume
  have he (t : ℝ) : ‖(w+t • v).1.2‖^p = F t := by
    rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)]
    exact integral_congr_ae ((hwg t).fun_comp (fun a => ‖a‖^p))
  have hzero : ‖w.1.2‖^p = F 0 := by simpa only [zero_smul, add_zero] using he 0
  have hlocal : IsLocalMin F 0 := by
    apply Eventually.of_forall
    intro t
    rw [←he t, ←hzero]
    exact hm (w+t • v) (ht t)
  have hd : HasDerivAt F (p*(∫ x, inner ℝ (pFlux p ((w.1.2 : Space n → Space n) x))
      (gradient φ x) ∂volume)) 0 := by
    convert! hasDerivAt_integral_energy_line hp (Lp.memLp w.1.2) hφg using 1 <;>
      simp only [F]
  have hh := hlocal.hasDerivAt_eq_zero hd
  exact (mul_eq_zero.mp hh).resolve_left (zero_lt_one.trans hp).ne'


theorem exteriorCapacityClass_minimum_weakPHarmonic {n : ℕ} (hp : 1 < p)
    (hpq : p ≤ q) {K : Set (Space n)} (hK : IsClosed K)
    (w : exteriorHomogeneousGraph p q n) (hw : w ∈ exteriorCapacityClass p q K)
    (hm : ∀ z ∈ exteriorCapacityClass p q K, ‖w.1.2‖^p ≤ ‖z.1.2‖^p) :
    WeakPHarmonicPair p Kᶜ (w.1.1 : Space n → ℝ) (w.1.2 : Space n → Space n) := by
  apply weakPHarmonicPair_of_smooth_test_equation hp hK.isOpen_compl
    (fun D hD => exteriorHomogeneousGraph_sobolev_on_bounded p q hp hpq w hD.2.1)
  intro D hD φ hφ
  have hφE : SmoothTest Kᶜ φ := ⟨hφ.1, hφ.2.1,
    hφ.2.2.trans (subset_closure.trans hD.2.2)⟩
  have he : (∫ x in D, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume) =
      ∫ x, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hg : gradient φ x = 0 := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
      (fun ht => hx (hφ.2.2 ht))
    simp only [fluxPairing, hg, inner_zero_right]
  rw [he]
  exact exteriorCapacityClass_minimum_smooth_equation p q hp w hw hm hφE

/-- Every compact K has a genuine global finite-energy variational capacity
minimizer in the subcritical range, with the actual weak exterior PDE and
actual capacity-preserving smooth graph approximation. This asserts no selected
continuous representative or pointwise boundary value at irregular points. -/
theorem exists_variational_capacity_potential {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hpn : p < (n : ℝ)) {K : Set (Space n)} (hK : IsCompact K) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      MemLp u (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume ∧
      MemLp g (ENNReal.ofReal p) volume ∧
      (∀ D : Set (Space n), Bornology.IsBounded D → SobolevPair p D u g) ∧
      WeakPHarmonicPair p Kᶜ u g ∧
      BMCompactCapacityV2.relativeCapacity p K univ = ENNReal.ofReal (∫ x, ‖g x‖^p ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ, (∀ j, BMCompactCapacityV2.Admissible K univ (φ j)) ∧
        Tendsto (fun j => eLpNorm (φ j-u) (ENNReal.ofReal ((n : ℝ)*p/((n : ℝ)-p))) volume)
          atTop (𝓝 0) ∧
        Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-g x) (ENNReal.ofReal p) volume)
          atTop (𝓝 0) := by
  let q : ℝ := (n : ℝ)*p/((n : ℝ)-p)
  have hpq : p ≤ q := by
    apply (le_div_iff₀ (sub_pos.mpr hpn)).mpr
    nlinarith [sq_nonneg p]
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr (hp.le.trans hpq)⟩
  obtain ⟨w, hw, hm⟩ := exists_exteriorCapacityClass_minimum p q hp hpn rfl hK
  have he := capacity_eq_exteriorCapacityClass_minimum_energy p q hp hw hm
  rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)] at he
  refine ⟨(w.1.1 : Space n → ℝ), (w.1.2 : Space n → Space n), Lp.memLp _, Lp.memLp _,
    (fun D hD => exteriorHomogeneousGraph_sobolev_on_bounded p q hp hpq w hD),
    exteriorCapacityClass_minimum_weakPHarmonic p q hp hpq hK.isClosed w hw hm, he, ?_⟩
  exact exteriorCapacityClass_smooth_approximation p q hw

end BMCompactPDE

end -- original noncomputable section
end ExteriorSegment_ExteriorCapacityMinimum

#print axioms BMCompactPDE.exists_exteriorPlateauClass_minimum_allp
#print axioms BMCompactPDE.exists_bounded_plateau_energy_minimum_allp
#print axioms BMCompactPDE.exists_bounded_plateau_harmonic_minimum_allp
#print axioms BMCompactPDE.exists_bounded_condenser_capacity_bound_allp
#print axioms BMCompactPDE.exists_exteriorHomogeneousEnergy_minimum
#print axioms BMCompactPDE.convex_exteriorCapacityClass
#print axioms BMCompactPDE.exteriorCapacityClass_nonempty
#print axioms BMCompactPDE.exteriorCapacityClass_smooth_approximation
#print axioms BMCompactPDE.exists_exteriorCapacityClass_minimum
#print axioms BMCompactPDE.capacity_eq_exteriorCapacityClass_minimum_energy
#print axioms BMCompactPDE.exteriorCapacityClass_minimum_weakPHarmonic
#print axioms BMCompactPDE.exists_variational_capacity_potential
