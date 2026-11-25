import ExteriorCapacityConstruction

/-! Actual all-p bounded relative-capacity attainment. The admissible class is
the strong W0(O) graph closure of ALL genuine smooth capacity admissibles for
K in O, including thin K. This does not substitute a.e. values on K for traces,
and asserts no continuous boundary representative or Green normalization. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal ContDiff
namespace BMCompactPDE

variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p)

set_option maxHeartbeats 1000000 in
theorem exists_w0Lp_constrained_energy_minimum_allp {n : ℕ} (hn : 2 ≤ n)
    {O : Set (Space n)} (hOb : Bornology.IsBounded O)
    {T : Set (w0LpGraph p hp n O)} (hne : T.Nonempty)
    (hclosed : IsClosed T) (hconv : Convex ℝ T) :
    ∃ w ∈ T, ∀ z ∈ T, ‖w.1.2‖^p ≤ ‖z.1.2‖^p := by
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
  have hbdd : BddBelow (J '' T) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hcoercive : ∀ a : ℝ, ∃ R : ℝ,
      ∀ w ∈ T, J w ≤ a → ‖w‖ ≤ R := by
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
      ∀ x ∈ T, ∀ y ∈ T,
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
    hne
    hclosed hconv
    hcont.continuousOn hbdd hcoercive hgap


def exteriorRelativeCapacitySmoothClass {n : ℕ} (K O : Set (Space n)) :
    Set (w0LpGraph p hp n O) :=
  {w | ∃ φ : Space n → ℝ, BMCompactCapacityV2.Admissible K O φ ∧
    (w.1.1 : Space n → ℝ) =ᵐ[volume.restrict O] φ ∧
    (w.1.2 : Space n → Space n) =ᵐ[volume.restrict O] gradient φ}

def exteriorRelativeCapacityClass {n : ℕ} (K O : Set (Space n)) :
    Set (w0LpGraph p hp n O) := closure (exteriorRelativeCapacitySmoothClass p hp K O)

private theorem exterior_relative_compactSupport_smul {n : ℕ} {f : Space n → ℝ}
    (hf : HasCompactSupport f) (c : ℝ) : HasCompactSupport (c • f) :=
  hf.isCompact.of_isClosed_subset (isClosed_tsupport (c • f))
    (tsupport_smul_subset_right (fun _ : Space n => c) f)

private theorem exteriorRelativeCapacityClass_node {n : ℕ} {K O : Set (Space n)}
    {φ : Space n → ℝ} (hφ : BMCompactCapacityV2.Admissible K O φ) :
    ∃ w : w0LpGraph p hp n O, w ∈ exteriorRelativeCapacitySmoothClass p hp K O ∧
      (w.1.1 : Space n → ℝ) =ᵐ[volume.restrict O] φ ∧
      (w.1.2 : Space n → Space n) =ᵐ[volume.restrict O] gradient φ := by
  have ht : SmoothTest O φ := ⟨hφ.1, hφ.2.1, hφ.2.2.1⟩
  obtain ⟨w, hwu, hwg⟩ := (ht.zeroBoundarySobolevPair hp).exists_w0LpGraph_representatives hp
  exact ⟨w, ⟨φ, hφ, hwu, hwg⟩, hwu, hwg⟩

theorem convex_exteriorRelativeCapacityClass {n : ℕ} (K O : Set (Space n)) :
    Convex ℝ (exteriorRelativeCapacityClass p hp K O) := by
  have hs : Convex ℝ (exteriorRelativeCapacitySmoothClass p hp K O) := by
    intro x hx y hy a b ha hb hab
    obtain ⟨φ, hφ, hxu, hxg⟩ := hx
    obtain ⟨ψ, hψ, hyu, hyg⟩ := hy
    let f : Space n → ℝ := a • φ+b • ψ
    have hf : BMCompactCapacityV2.Admissible K O f := by
      refine ⟨(hφ.1.const_smul a).add (hψ.1.const_smul b),
        (exterior_relative_compactSupport_smul hφ.2.1 a).add
          (exterior_relative_compactSupport_smul hψ.2.1 b), ?_, ?_⟩
      · exact (tsupport_add _ _).trans (union_subset
          ((tsupport_smul_subset_right (fun _ : Space n => a) φ).trans hφ.2.2.1)
          ((tsupport_smul_subset_right (fun _ : Space n => b) ψ).trans hψ.2.2.1))
      · intro z hz
        have hh := add_le_add (mul_le_mul_of_nonneg_left (hφ.2.2.2 z hz) ha)
          (mul_le_mul_of_nonneg_left (hψ.2.2.2 z hz) hb)
        simpa only [f, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, hab] using hh
    refine ⟨f, hf, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_add (a • x.1.1) (b • y.1.1),
        Lp.coeFn_smul a x.1.1, Lp.coeFn_smul b y.1.1, hxu, hyu]
        with z hadd hax hby hx hy
      change ((a • x.1.1+b • y.1.1 : ScalarLp p n O) : Space n → ℝ) z = f z
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hax, hby]
      simp only [f, Pi.add_apply, Pi.smul_apply, hx, hy]
    · filter_upwards [Lp.coeFn_add (a • x.1.2) (b • y.1.2),
        Lp.coeFn_smul a x.1.2, Lp.coeFn_smul b y.1.2, hxg, hyg]
        with z hadd hax hby hx hy
      change ((a • x.1.2+b • y.1.2 : VectorLp p n O) : Space n → Space n) z = gradient f z
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

theorem exteriorRelativeCapacityClass_nonempty {n : ℕ} {K O : Set (Space n)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    (exteriorRelativeCapacityClass p hp K O).Nonempty := by
  obtain ⟨φ, hφ⟩ := BMCompactCapacityV2.exists_admissible_of_isCompact hK hO hKO
  obtain ⟨w, hw, _, _⟩ := exteriorRelativeCapacityClass_node p hp hφ
  exact ⟨w, subset_closure hw⟩

theorem exteriorRelativeCapacityClass_smooth_approximation {n : ℕ} {K O : Set (Space n)}
    {w : w0LpGraph p hp n O} (hw : w ∈ exteriorRelativeCapacityClass p hp K O) :
    ∃ φ : ℕ → Space n → ℝ, (∀ j, BMCompactCapacityV2.Admissible K O (φ j)) ∧
      Tendsto (fun j => eLpNorm (φ j-(w.1.1 : Space n → ℝ)) (ENNReal.ofReal p) (volume.restrict O))
        atTop (𝓝 0) ∧
      Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-(w.1.2 : Space n → Space n) x)
        (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) := by
  obtain ⟨z, hz, hl⟩ := mem_closure_iff_seq_limit.mp hw
  choose φ hφ hzu hzg using hz
  have h1 := (continuous_fst.tendsto w.1).comp ((continuous_subtype_val.tendsto w).comp hl)
  have h2 := (continuous_snd.tendsto w.1).comp ((continuous_subtype_val.tendsto w).comp hl)
  have hl1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (z j).1.1) w.1.1).mp h1
  have hl2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => (z j).1.2) w.1.2).mp h2
  refine ⟨φ, hφ, ?_, ?_⟩
  · have he (j : ℕ) : eLpNorm (φ j-(w.1.1 : Space n → ℝ)) (ENNReal.ofReal p) (volume.restrict O) =
        eLpNorm (((z j).1.1 : Space n → ℝ)-(w.1.1 : Space n → ℝ)) (ENNReal.ofReal p) (volume.restrict O) :=
      eLpNorm_congr_ae ((hzu j).symm.sub EventuallyEq.rfl)
    simpa only [he] using hl1
  · have he (j : ℕ) : eLpNorm (fun x => gradient (φ j) x-(w.1.2 : Space n → Space n) x)
        (ENNReal.ofReal p) (volume.restrict O) =
        eLpNorm (((z j).1.2 : Space n → Space n)-(w.1.2 : Space n → Space n)) (ENNReal.ofReal p) (volume.restrict O) :=
      eLpNorm_congr_ae ((hzg j).symm.sub EventuallyEq.rfl)
    simpa only [he] using hl2

theorem exists_exteriorRelativeCapacityClass_minimum {n : ℕ} (hn : 2 ≤ n)
    {K O : Set (Space n)} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hOb : Bornology.IsBounded O) :
    ∃ w ∈ exteriorRelativeCapacityClass p hp K O,
      ∀ z ∈ exteriorRelativeCapacityClass p hp K O, ‖w.1.2‖^p ≤ ‖z.1.2‖^p := by
  exact exists_w0Lp_constrained_energy_minimum_allp p hp hn hOb
    (exteriorRelativeCapacityClass_nonempty p hp hK hO hKO)
    isClosed_closure (convex_exteriorRelativeCapacityClass p hp K O)

theorem relativeCapacity_eq_exteriorRelativeCapacityClass_minimum_energy
    {n : ℕ} {K O : Set (Space n)} {w : w0LpGraph p hp n O}
    (hw : w ∈ exteriorRelativeCapacityClass p hp K O)
    (hm : ∀ z ∈ exteriorRelativeCapacityClass p hp K O, ‖w.1.2‖^p ≤ ‖z.1.2‖^p) :
    BMCompactCapacityV2.relativeCapacity p K O = ENNReal.ofReal (‖w.1.2‖^p) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  let J : w0LpGraph p hp n O → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z.1.2‖^p)
  have hJ : Continuous J := ENNReal.continuous_ofReal.comp
    ((w0LpGradient p hp n O).continuous.norm.rpow_const (fun _ => Or.inr hp0.le))
  have hE (z : w0LpGraph p hp n O) (φ : Space n → ℝ)
      (hφ : BMCompactCapacityV2.Admissible K O φ)
      (hzg : (z.1.2 : Space n → Space n) =ᵐ[volume.restrict O] gradient φ) :
      BMCompactCapacityV2.pEnergy p O φ = J z := by
    have hg : MemLp (gradient φ) (ENNReal.ofReal p) (volume.restrict O) :=
      (BMCompactCapacityV2.gradient_smooth_compactSupport_memLp (ENNReal.ofReal p) hφ.1 hφ.2.1).restrict O
    have he : BMCompactCapacityV2.pEnergy p O φ = ENNReal.ofReal (∫ x in O, ‖gradient φ x‖^p ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal (integrable_norm_rpow_of_memLp hp hg)
        (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) p))).symm
    rw [he]
    change ENNReal.ofReal (∫ x in O, ‖gradient φ x‖^p ∂volume) = ENNReal.ofReal (‖z.1.2‖^p)
    congr 1
    rw [BMCompactNonlinear.lp_norm_rpow_eq_integral hp0]
    exact (integral_congr_ae (hzg.fun_comp (fun a => ‖a‖^p))).symm
  apply le_antisymm
  · have hs : exteriorRelativeCapacitySmoothClass p hp K O ⊆
        {z | BMCompactCapacityV2.relativeCapacity p K O ≤ J z} := by
      rintro z ⟨φ, hφ, _, hzg⟩
      exact (BMCompactCapacityV2.relativeCapacity_le_energy p hφ).trans_eq (hE z φ hφ hzg)
    exact (closure_minimal hs (isClosed_le continuous_const hJ)) hw
  · unfold BMCompactCapacityV2.relativeCapacity
    apply le_iInf
    intro φ
    apply le_iInf
    intro hφ
    obtain ⟨v, hv, _, hvg⟩ := exteriorRelativeCapacityClass_node p hp hφ
    exact (ENNReal.ofReal_le_ofReal (hm v (subset_closure hv))).trans_eq (hE v φ hφ hvg).symm

private theorem exteriorRelativeCapacityClass_add_smooth_off {n : ℕ}
    {K O : Set (Space n)} {w v : w0LpGraph p hp n O}
    (hw : w ∈ exteriorRelativeCapacityClass p hp K O)
    {φ : Space n → ℝ} (hφ : SmoothTest (O \ K) φ)
    (hvu : (v.1.1 : Space n → ℝ) =ᵐ[volume.restrict O] φ)
    (hvg : (v.1.2 : Space n → Space n) =ᵐ[volume.restrict O] gradient φ) (t : ℝ) :
    w+t • v ∈ exteriorRelativeCapacityClass p hp K O := by
  have hφ0 (x : Space n) (hx : x ∈ K) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => (hφ.2.2 ht).2 hx)
  have hpres : exteriorRelativeCapacitySmoothClass p hp K O ⊆
      (fun z => z+t • v) ⁻¹' exteriorRelativeCapacityClass p hp K O := by
    rintro z ⟨ψ, hψ, hzu, hzg⟩
    have hf : BMCompactCapacityV2.Admissible K O (ψ+t • φ) := by
      refine ⟨hψ.1.add (hφ.1.const_smul t),
        hψ.2.1.add (exterior_relative_compactSupport_smul hφ.2.1 t), ?_, ?_⟩
      · exact (tsupport_add _ _).trans (union_subset hψ.2.2.1
          ((tsupport_smul_subset_right (fun _ : Space n => t) φ).trans (hφ.2.2.trans diff_subset)))
      · intro x hx
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hφ0 x hx,
          mul_zero, add_zero] using hψ.2.2.2 x hx
    apply subset_closure
    refine ⟨ψ+t • φ, hf, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_add z.1.1 (t • v.1.1), Lp.coeFn_smul t v.1.1, hzu, hvu]
        with x ha hs hz hv
      change ((z.1.1+t • v.1.1 : ScalarLp p n O) : Space n → ℝ) x = _
      rw [ha]
      simp only [Pi.add_apply]
      rw [hs]
      simp only [Pi.add_apply, Pi.smul_apply, hz, hv]
    · filter_upwards [Lp.coeFn_add z.1.2 (t • v.1.2), Lp.coeFn_smul t v.1.2, hzg, hvg]
        with x ha hs hz hv
      change ((z.1.2+t • v.1.2 : VectorLp p n O) : Space n → Space n) x = _
      rw [ha]
      simp only [Pi.add_apply]
      rw [hs]
      simp only [Pi.smul_apply, hz, hv]
      rw [gradient_add_smooth_actual (f := ψ) (h := t • φ) hψ.1 (hφ.1.const_smul t), gradient_smul_smooth_actual hφ.1 t]
      rfl
  have hc : Continuous (fun z : w0LpGraph p hp n O => z+t • v) :=
    continuous_id.add continuous_const
  exact (closure_minimal hpres (isClosed_closure.preimage hc)) hw

set_option maxHeartbeats 1000000 in
private theorem exteriorRelativeCapacityClass_minimum_smooth_equation {n : ℕ}
    {K O : Set (Space n)} (w : w0LpGraph p hp n O)
    (hw : w ∈ exteriorRelativeCapacityClass p hp K O)
    (hm : ∀ z ∈ exteriorRelativeCapacityClass p hp K O, ‖w.1.2‖^p ≤ ‖z.1.2‖^p)
    {φ : Space n → ℝ} (hφ : SmoothTest (O \ K) φ) :
    (∫ x in O, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume) = 0 := by
  have hφO : SmoothTest O φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans diff_subset⟩
  have hφW := hφO.zeroBoundarySobolevPair hp
  obtain ⟨v, hvu, hvg⟩ := hφW.exists_w0LpGraph_representatives hp
  have hwg (t : ℝ) : ((w+t • v).1.2 : Space n → Space n) =ᵐ[volume.restrict O]
      (fun x => (w.1.2 : Space n → Space n) x+t • gradient φ x) := by
    filter_upwards [Lp.coeFn_add w.1.2 (t • v.1.2), Lp.coeFn_smul t v.1.2, hvg]
      with x ha hs hv
    change ((w.1.2+t • v.1.2 : VectorLp p n O) : Space n → Space n) x = _
    rw [ha]
    simp only [Pi.add_apply]
    rw [hs]
    simp only [Pi.smul_apply, hv]
  have ht (t : ℝ) : w+t • v ∈ exteriorRelativeCapacityClass p hp K O :=
    exteriorRelativeCapacityClass_add_smooth_off p hp hw hφ hvu hvg t
  let F : ℝ → ℝ := fun t => ∫ x in O, ‖(w.1.2 : Space n → Space n) x+t • gradient φ x‖^p ∂volume
  have he (t : ℝ) : ‖(w+t • v).1.2‖^p = F t := by
    rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)]
    exact integral_congr_ae ((hwg t).fun_comp (fun a => ‖a‖^p))
  have hzero : ‖w.1.2‖^p = F 0 := by simpa only [zero_smul, add_zero] using he 0
  have hlocal : IsLocalMin F 0 := by
    apply Eventually.of_forall
    intro t
    rw [←he t, ←hzero]
    exact hm (w+t • v) (ht t)
  have hd : HasDerivAt F (p*(∫ x in O, inner ℝ (pFlux p ((w.1.2 : Space n → Space n) x))
      (gradient φ x) ∂volume)) 0 := by
    convert! hasDerivAt_integral_energy_line hp (Lp.memLp w.1.2) hφW.1.2.2.1 using 1 <;>
      simp only [F]
  have hh := hlocal.hasDerivAt_eq_zero hd
  exact (mul_eq_zero.mp hh).resolve_left (zero_lt_one.trans hp).ne'

theorem exteriorRelativeCapacityClass_minimum_weakPHarmonic {n : ℕ}
    {K O : Set (Space n)} (hK : IsClosed K) (hO : IsOpen O)
    (w : w0LpGraph p hp n O) (hw : w ∈ exteriorRelativeCapacityClass p hp K O)
    (hm : ∀ z ∈ exteriorRelativeCapacityClass p hp K O, ‖w.1.2‖^p ≤ ‖z.1.2‖^p) :
    WeakPHarmonicPair p (O \ K) (w.1.1 : Space n → ℝ) (w.1.2 : Space n → Space n) := by
  have he : ∀ φ : Space n → ℝ, SmoothTest (O \ K) φ →
      (∫ x in O \ K, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume) =
        (0 : ℝ)*(∫ x in O \ K, φ x ∂volume) := by
    intro φ hφ
    have hzero (x : Space n) (hx : x ∉ O \ K) :
        fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x = 0 := by
      have hg : gradient φ x = 0 := BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport
        (fun ht => hx (hφ.2.2 ht))
      simp only [fluxPairing, hg, inner_zero_right]
    have hIntD : (∫ x in O \ K, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume) =
        ∫ x, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hzero
    have hIntO : (∫ x in O, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume) =
        ∫ x, fluxPairing p (w.1.2 : Space n → Space n) (gradient φ) x ∂volume :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hzero x (fun hd => hx hd.1))
    rw [hIntD, ←hIntO, exteriorRelativeCapacityClass_minimum_smooth_equation p hp w hw hm hφ, zero_mul]
  exact (weakPSourcePair_of_sobolev_smooth_source_equation (hO.sdiff hK)
    (w.2.1.mono_actual diff_subset) he).harmonic_of_source_zero

/-- Actual bounded relative-capacity attainment for every p>1,n>=2 and
arbitrary compact K inside bounded open O. The trace is retained as genuine
capacity-admissible smooth graph approximation, without a pointwise claim. -/
theorem exists_bounded_relative_capacity_potential_allp {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hn : 2 ≤ n) {K O : Set (Space n)}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) (hOb : Bornology.IsBounded O) :
    ∃ u : Space n → ℝ, ∃ g : Space n → Space n,
      ZeroBoundarySobolevPair p O u g ∧
      WeakPHarmonicPair p (O \ K) u g ∧
      BMCompactCapacityV2.relativeCapacity p K O = ENNReal.ofReal (∫ x in O, ‖g x‖^p ∂volume) ∧
      ∃ φ : ℕ → Space n → ℝ, (∀ j, BMCompactCapacityV2.Admissible K O (φ j)) ∧
        Tendsto (fun j => eLpNorm (φ j-u) (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) ∧
        Tendsto (fun j => eLpNorm (fun x => gradient (φ j) x-g x)
          (ENNReal.ofReal p) (volume.restrict O)) atTop (𝓝 0) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp.le⟩
  obtain ⟨w, hw, hm⟩ := exists_exteriorRelativeCapacityClass_minimum p hp hn hK hO hKO hOb
  have he := relativeCapacity_eq_exteriorRelativeCapacityClass_minimum_energy p hp hw hm
  rw [BMCompactNonlinear.lp_norm_rpow_eq_integral (zero_lt_one.trans hp)] at he
  exact ⟨(w.1.1 : Space n → ℝ), (w.1.2 : Space n → Space n), w.2,
    exteriorRelativeCapacityClass_minimum_weakPHarmonic p hp hK.isClosed hO w hw hm, he,
    exteriorRelativeCapacityClass_smooth_approximation p hp hw⟩

end BMCompactPDE
#print axioms BMCompactPDE.exists_w0Lp_constrained_energy_minimum_allp
#print axioms BMCompactPDE.convex_exteriorRelativeCapacityClass
#print axioms BMCompactPDE.exteriorRelativeCapacityClass_nonempty
#print axioms BMCompactPDE.exteriorRelativeCapacityClass_smooth_approximation
#print axioms BMCompactPDE.exists_exteriorRelativeCapacityClass_minimum
#print axioms BMCompactPDE.relativeCapacity_eq_exteriorRelativeCapacityClass_minimum_energy
#print axioms BMCompactPDE.exteriorRelativeCapacityClass_minimum_weakPHarmonic
#print axioms BMCompactPDE.exists_bounded_relative_capacity_potential_allp
