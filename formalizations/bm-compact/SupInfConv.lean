import ContactForcedComparison
import PropagationTranslationCalculus
import BMCompactChecked

/-! Sup-convolution and inf-convolution on compact subsets of `Space n`:
attainment, uniform convergence, global semiconvexity/semiconcavity with
explicit Lipschitz constants, and preservation of viscosity subsolution and
positive-source weak-supersolution contact inequalities. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal NNReal
namespace BMCompactPDE

section Basic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Sup-convolution of `u` over a set `K` with parameter `ε`. -/
def supConv (K : Set E) (ε : ℝ) (u : E → ℝ) (x : E) : ℝ :=
  sSup ((fun y => u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2) '' K)

/-- Inf-convolution of `v` over a set `K` with parameter `ε`. -/
def infConv (K : Set E) (ε : ℝ) (v : E → ℝ) (x : E) : ℝ :=
  -supConv K ε (-v) x

theorem supConv_bddAbove {K : Set E} (hK : IsCompact K) {ε : ℝ}
    {u : E → ℝ} (hu : ContinuousOn u K) (x : E) :
    BddAbove ((fun y => u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2) '' K) := by
  have hcont : ContinuousOn (fun y => u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2) K :=
    hu.sub (continuousOn_const.mul ((continuous_const.sub continuous_id).norm.pow 2).continuousOn)
  exact (hK.image_of_continuousOn hcont).bddAbove

theorem le_supConv {K : Set E} (hK : IsCompact K) {ε : ℝ}
    {u : E → ℝ} (hu : ContinuousOn u K) (x : E) {y : E} (hy : y ∈ K) :
    u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2 ≤ supConv K ε u x :=
  le_csSup (supConv_bddAbove hK hu x) ⟨y, hy, rfl⟩

theorem self_le_supConv {K : Set E} (hK : IsCompact K) {ε : ℝ}
    {u : E → ℝ} (hu : ContinuousOn u K) {x : E} (hx : x ∈ K) :
    u x ≤ supConv K ε u x := by
  simpa using le_supConv hK hu x hx

theorem supConv_attained {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) {ε : ℝ}
    {u : E → ℝ} (hu : ContinuousOn u K) (x : E) :
    ∃ y ∈ K, supConv K ε u x = u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2 := by
  have hcont : ContinuousOn (fun y => u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2) K :=
    hu.sub (continuousOn_const.mul ((continuous_const.sub continuous_id).norm.pow 2).continuousOn)
  obtain ⟨y, hyK, hymax⟩ := hK.exists_isMaxOn hne hcont
  refine ⟨y, hyK, le_antisymm ?_ (le_supConv hK hu x hyK)⟩
  apply csSup_le (hne.image _)
  rintro _ ⟨z, hzK, rfl⟩
  exact hymax hzK

theorem supConv_add_quad_eq {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) {ε : ℝ}
    {u : E → ℝ} (hu : ContinuousOn u K) (x : E) :
    supConv K ε u x + (1 / (2 * ε)) * ‖x‖ ^ 2 =
      sSup ((fun y => u y - (1 / (2 * ε)) * ‖y‖ ^ 2 + (1 / ε) * inner ℝ x y) '' K) := by
  have hquad (y : E) :
      (u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2) + (1 / (2 * ε)) * ‖x‖ ^ 2 =
        u y - (1 / (2 * ε)) * ‖y‖ ^ 2 + (1 / ε) * inner ℝ x y := by
    rw [norm_sub_sq_real]; ring
  obtain ⟨y₀, hy₀, hmax⟩ := supConv_attained hK hne hu x
  have hbdd : BddAbove ((fun y => u y - (1 / (2 * ε)) * ‖y‖ ^ 2 + (1 / ε) * inner ℝ x y) '' K) := by
    have hc : ContinuousOn (fun y => u y - (1 / (2 * ε)) * ‖y‖ ^ 2 + (1 / ε) * inner ℝ x y) K :=
      (hu.sub (continuousOn_const.mul (continuous_norm.pow 2).continuousOn)).add
        (continuousOn_const.mul (continuous_const.inner continuous_id).continuousOn)
    exact (hK.image_of_continuousOn hc).bddAbove
  apply le_antisymm
  · rw [hmax, hquad y₀]
    exact le_csSup hbdd ⟨y₀, hy₀, rfl⟩
  · apply csSup_le (hne.image _)
    rintro _ ⟨z, hzK, rfl⟩
    dsimp only
    rw [← hquad z]
    linarith [le_supConv (ε := ε) hK hu x hzK]

theorem supConv_semiconvex_convexOn {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {ε : ℝ} {u : E → ℝ} (hu : ContinuousOn u K) :
    ConvexOn ℝ univ (fun x => supConv K ε u x + (1 / (2 * ε)) * ‖x‖ ^ 2) := by
  refine ⟨convex_univ, fun x₁ _ x₂ _ a b ha hb hab => ?_⟩
  dsimp only
  simp only [smul_eq_mul]
  rw [supConv_add_quad_eq hK hne hu (a • x₁ + b • x₂)]
  apply csSup_le (hne.image _)
  rintro _ ⟨y, hyK, rfl⟩
  have h1 : u y - (1 / (2 * ε)) * ‖y‖ ^ 2 + (1 / ε) * inner ℝ x₁ y ≤
      supConv K ε u x₁ + (1 / (2 * ε)) * ‖x₁‖ ^ 2 := by
    rw [supConv_add_quad_eq hK hne hu x₁]
    have hc : ContinuousOn (fun z => u z - (1 / (2 * ε)) * ‖z‖ ^ 2 + (1 / ε) * inner ℝ x₁ z) K :=
      (hu.sub (continuousOn_const.mul (continuous_norm.pow 2).continuousOn)).add
        (continuousOn_const.mul (continuous_const.inner continuous_id).continuousOn)
    exact le_csSup (hK.image_of_continuousOn hc).bddAbove ⟨y, hyK, rfl⟩
  have h2 : u y - (1 / (2 * ε)) * ‖y‖ ^ 2 + (1 / ε) * inner ℝ x₂ y ≤
      supConv K ε u x₂ + (1 / (2 * ε)) * ‖x₂‖ ^ 2 := by
    rw [supConv_add_quad_eq hK hne hu x₂]
    have hc : ContinuousOn (fun z => u z - (1 / (2 * ε)) * ‖z‖ ^ 2 + (1 / ε) * inner ℝ x₂ z) K :=
      (hu.sub (continuousOn_const.mul (continuous_norm.pow 2).continuousOn)).add
        (continuousOn_const.mul (continuous_const.inner continuous_id).continuousOn)
    exact le_csSup (hK.image_of_continuousOn hc).bddAbove ⟨y, hyK, rfl⟩
  dsimp only
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hid : u y - (1 / (2 * ε)) * ‖y‖ ^ 2 + (1 / ε) * (a * inner ℝ x₁ y + b * inner ℝ x₂ y) =
      a * (u y - (1 / (2 * ε)) * ‖y‖ ^ 2 + (1 / ε) * inner ℝ x₁ y) +
      b * (u y - (1 / (2 * ε)) * ‖y‖ ^ 2 + (1 / ε) * inner ℝ x₂ y) := by
    have hb' : b = 1 - a := by linarith
    rw [hb']; ring
  rw [hid]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

theorem supConv_semiconvex_lipschitzWith {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) (hKR : ∀ y ∈ K, ‖y‖ ≤ R)
    {u : E → ℝ} (hu : ContinuousOn u K) :
    LipschitzWith (⟨R / ε, by positivity⟩ : ℝ≥0) (fun x => supConv K ε u x + (1 / (2 * ε)) * ‖x‖ ^ 2) := by
  refine LipschitzWith.of_dist_le_mul fun x₁ x₂ => ?_
  change dist _ _ ≤ (R / ε) * dist x₁ x₂
  rw [Real.dist_eq, dist_eq_norm]
  have hone (a b : E) :
      (supConv K ε u a + (1 / (2 * ε)) * ‖a‖ ^ 2) -
        (supConv K ε u b + (1 / (2 * ε)) * ‖b‖ ^ 2) ≤ (R / ε) * ‖a - b‖ := by
    obtain ⟨y, hyK, hmax⟩ := supConv_attained (ε := ε) hK hne hu a
    have hle := le_supConv (ε := ε) hK hu b hyK
    have hq (x : E) :
        (u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2) + (1 / (2 * ε)) * ‖x‖ ^ 2 =
          u y - (1 / (2 * ε)) * ‖y‖ ^ 2 + (1 / ε) * inner ℝ x y := by
      rw [norm_sub_sq_real]; ring
    have hdiff : (supConv K ε u a + (1 / (2 * ε)) * ‖a‖ ^ 2) -
        (supConv K ε u b + (1 / (2 * ε)) * ‖b‖ ^ 2) ≤ (1 / ε) * inner ℝ (a - b) y := by
      rw [inner_sub_left]
      have ha_eq := hq a
      have hb_eq := hq b
      linarith
    have hcs : inner ℝ (a - b) y ≤ ‖a - b‖ * R :=
      (real_inner_le_norm (a - b) y).trans (mul_le_mul_of_nonneg_left (hKR y hyK) (norm_nonneg _))
    calc (supConv K ε u a + (1 / (2 * ε)) * ‖a‖ ^ 2) -
          (supConv K ε u b + (1 / (2 * ε)) * ‖b‖ ^ 2)
        ≤ (1 / ε) * inner ℝ (a - b) y := hdiff
      _ ≤ (1 / ε) * (‖a - b‖ * R) := mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (R / ε) * ‖a - b‖ := by ring
  rw [abs_le]
  constructor
  · have h := hone x₂ x₁
    rw [norm_sub_rev] at h
    linarith
  · exact hone x₁ x₂

theorem supConv_maximizer_dist_sq_le {K : Set E} (hK : IsCompact K) {ε M : ℝ} (hε : 0 < ε)
    {u : E → ℝ} (hu : ContinuousOn u K) (hM : ∀ z ∈ K, |u z| ≤ M)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K)
    (hmax : supConv K ε u x = u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2) :
    ‖x - y‖ ^ 2 ≤ 4 * M * ε := by
  have h1 : u x ≤ u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2 := by
    rw [← hmax]; exact self_le_supConv hK hu hx
  have h2 : u y - u x ≤ 2 * M := by
    have hxM := abs_le.mp (hM x hx)
    have hyM := abs_le.mp (hM y hy)
    linarith
  have h3 : (1 / (2 * ε)) * ‖x - y‖ ^ 2 ≤ 2 * M := by linarith
  have h4 : 0 < 2 * ε := by positivity
  rw [one_div, inv_mul_le_iff₀ h4] at h3
  linarith

theorem supConv_uniform_close {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {u : E → ℝ} (hu : ContinuousOn u K) {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ x ∈ K, u x ≤ supConv K ε u x ∧ supConv K ε u x ≤ u x + η := by
  have huc : UniformContinuousOn u K := hK.uniformContinuousOn_of_continuous hu
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδu⟩ := huc η hη
  obtain ⟨M, hMpos, hM⟩ : ∃ M : ℝ, 0 < M ∧ ∀ z ∈ K, |u z| ≤ M := by
    obtain ⟨z₀, -, hzmax⟩ := hK.exists_isMaxOn hne hu.abs
    refine ⟨|u z₀| + 1, by positivity, fun z hz => ?_⟩
    have hle : |u z| ≤ |u z₀| := hzmax hz
    linarith
  refine ⟨δ ^ 2 / (4 * M), by positivity, fun ε hε hεlt x hx => ?_⟩
  refine ⟨self_le_supConv hK hu hx, ?_⟩
  obtain ⟨y, hyK, hmax⟩ := supConv_attained hK hne hu x
  have hsq := supConv_maximizer_dist_sq_le hK hε hu hM hx hyK hmax
  have hdist : dist y x < δ := by
    rw [dist_comm, dist_eq_norm]
    have hlt : ‖x - y‖ ^ 2 < δ ^ 2 := by
      have h4M : 0 < 4 * M := by positivity
      calc ‖x - y‖ ^ 2 ≤ 4 * M * ε := hsq
        _ < 4 * M * (δ ^ 2 / (4 * M)) := mul_lt_mul_of_pos_left hεlt h4M
        _ = δ ^ 2 := by field_simp [h4M.ne']
    nlinarith [norm_nonneg (x - y)]
  have hclose := hδu y hyK x hx hdist
  rw [Real.dist_eq] at hclose
  have huy : u y ≤ u x + η := by linarith [(abs_lt.mp hclose).2]
  have hpen : 0 ≤ (1 / (2 * ε)) * ‖x - y‖ ^ 2 := by positivity
  linarith

theorem infConv_le {K : Set E} (hK : IsCompact K) {ε : ℝ}
    {v : E → ℝ} (hv : ContinuousOn v K) (x : E) {y : E} (hy : y ∈ K) :
    infConv K ε v x ≤ v y + (1 / (2 * ε)) * ‖x - y‖ ^ 2 := by
  have h := le_supConv (ε := ε) hK hv.neg x hy
  dsimp only [infConv, Pi.neg_apply] at h ⊢; linarith

theorem infConv_le_self {K : Set E} (hK : IsCompact K) {ε : ℝ}
    {v : E → ℝ} (hv : ContinuousOn v K) {x : E} (hx : x ∈ K) :
    infConv K ε v x ≤ v x := by
  simpa using infConv_le hK hv x hx

theorem infConv_attained {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) {ε : ℝ}
    {v : E → ℝ} (hv : ContinuousOn v K) (x : E) :
    ∃ y ∈ K, infConv K ε v x = v y + (1 / (2 * ε)) * ‖x - y‖ ^ 2 := by
  obtain ⟨y, hyK, hmax⟩ := supConv_attained (ε := ε) hK hne hv.neg x
  refine ⟨y, hyK, ?_⟩
  dsimp only [infConv, Pi.neg_apply] at hmax ⊢; linarith

theorem infConv_uniform_close {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {v : E → ℝ} (hv : ContinuousOn v K) {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ x ∈ K, v x - η ≤ infConv K ε v x ∧ infConv K ε v x ≤ v x := by
  obtain ⟨ε₀, hε₀, hclose⟩ := supConv_uniform_close hK hne hv.neg hη
  refine ⟨ε₀, hε₀, fun ε hε hεlt x hx => ?_⟩
  have ⟨h1, h2⟩ := hclose ε hε hεlt x hx
  dsimp only [infConv, Pi.neg_apply] at h1 h2 ⊢
  constructor <;> linarith

end Basic

section ViscosityPreservation
variable {n : ℕ}

/-- Sup-convolution preserves `IsViscosityPSubsolution` on an open set `D`
whenever every maximizer for `x ∈ D` lies in `interior K ∩ Ω`. -/
theorem supConv_isViscosityPSubsolution {p ε : ℝ} {Ω D K : Set (Space n)}
    {u : Space n → ℝ} (hu : BMCompactAnalytic.IsViscosityPSubsolution p Ω u)
    (hD : IsOpen D) (hK : IsCompact K) (hne : K.Nonempty) (huc : ContinuousOn u K)
    (hε : 0 < ε)
    (hmax_in : ∀ x ∈ D, ∀ y ∈ K,
      supConv K ε u x = u y - (1 / (2 * ε)) * ‖x - y‖ ^ 2 → y ∈ interior K ∧ y ∈ Ω) :
    BMCompactAnalytic.IsViscosityPSubsolution p D (supConv K ε u) := by
  obtain ⟨R, hR, hKR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ y ∈ K, ‖y‖ ≤ R := by
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space n)
    refine ⟨max R 0, le_max_right _ _, fun y hy => ?_⟩
    have h1 : ‖y‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hR hy
    exact h1.trans (le_max_left _ _)
  have hcont : Continuous (supConv K ε u) := by
    have hlip := supConv_semiconvex_lipschitzWith hK hne hε hR hKR huc
    have hq : Continuous (fun x : Space n => (1 / (2 * ε)) * ‖x‖ ^ 2) :=
      continuous_const.mul (continuous_norm.pow 2)
    have h1 : Continuous (fun x : Space n =>
        (supConv K ε u x + (1 / (2 * ε)) * ‖x‖ ^ 2) - (1 / (2 * ε)) * ‖x‖ ^ 2) :=
      hlip.continuous.sub hq
    simpa only [add_sub_cancel_right] using h1
  refine ⟨hu.1, hD, hcont.continuousOn.upperSemicontinuousOn, ?_⟩
  intro x hxD φ hφ hcontact hupper hgφ
  obtain ⟨y, hyK, hmax⟩ := supConv_attained hK hne huc x
  obtain ⟨hyInt, hyΩ⟩ := hmax_in x hxD y hyK hmax
  let c : ℝ := (1 / (2 * ε)) * ‖x - y‖ ^ 2
  let ψ : Space n → ℝ := fun z => φ (z + x - y) + c
  have hψ2 : ContDiffAt ℝ 2 ψ y :=
    BMCompactAnalytic.contDiffAt_diagonal_translate_add_const hφ c
  have hψy : u y = ψ y := by
    dsimp only [ψ, c]
    rw [show y + x - y = x by abel]
    linarith
  have hψupper : ∀ᶠ z in 𝓝 y, u z ≤ ψ z := by
    have hshift : Tendsto (fun z : Space n => z + x - y) (𝓝 y) (𝓝 x) := by
      have hc : Continuous (fun z : Space n => z + x - y) :=
        (continuous_id.add continuous_const).sub continuous_const
      simpa [show y + x - y = x by abel] using (hc.continuousAt (x := y)).tendsto
    filter_upwards [mem_interior_iff_mem_nhds.mp hyInt, hshift.eventually hupper] with z hzK hzφ
    have hle := le_supConv (ε := ε) hK huc (z + x - y) hzK
    have hdiff : (z + x - y) - z = x - y := by abel
    rw [hdiff] at hle
    dsimp only [ψ, c]
    linarith
  have hψg : gradient ψ y ≠ 0 := by
    dsimp only [ψ]
    rw [BMCompactAnalytic.gradient_diagonal_translate_add_const]
    exact hgφ
  have hres := hu.2.2.2 y hyΩ ψ hψ2 hψy hψupper hψg
  dsimp only [ψ] at hres
  rwa [BMCompactAnalytic.normalizedPLaplacian_diagonal_translate_add_const] at hres

/-- Inf-convolution preserves the positive-source weak-supersolution strict
lower-contact inequality (including flat/critical tests!). -/
theorem infConv_le_neg_divergence_at_strict_contact {p c ε : ℝ} {Ω D K : Set (Space n)}
    {v : Space n → ℝ} {g : Space n → Space n}
    (hv : WeakPSourceSupersolutionPair p c Ω v g) (hvc : ContinuousOn v Ω)
    (hn : 2 ≤ n) (hD : IsOpen D) (hK : IsCompact K) (hne : K.Nonempty) (hKΩ : K ⊆ Ω)
    (hε : 0 < ε) {x : Space n} (hx : x ∈ D)
    (hmin_in : ∀ z ∈ K,
      infConv K ε v x = v z + (1 / (2 * ε)) * ‖x - z‖ ^ 2 → z ∈ interior K)
    {φ : Space n → ℝ} (hφ : ContDiffOn ℝ 1 φ D)
    (hF : ContDiffOn ℝ 1 (fun y => pFlux p (gradient φ y)) D)
    (htouch : infConv K ε v x = φ x) (hstrict : ∀ y ∈ D, y ≠ x → φ y < infConv K ε v y) :
    c ≤ -coordinateDivergence (fun y => pFlux p (gradient φ y)) x := by
  obtain ⟨z, hzK, hmin⟩ := infConv_attained hK hne (hvc.mono hKΩ) x
  have hzInt : z ∈ interior K := hmin_in z hzK hmin
  have hzΩ : z ∈ Ω := hKΩ hzK
  let d : ℝ := (1 / (2 * ε)) * ‖x - z‖ ^ 2
  let ψ : Space n → ℝ := fun w => φ (w + x - z) - d
  let T : Space n → Space n := fun w => w + x - z
  have hTcont : Continuous T := (continuous_id.add continuous_const).sub continuous_const
  have hTx : T z = x := by dsimp only [T]; abel
  let U : Set (Space n) := interior K ∩ T ⁻¹' D
  have hUopen : IsOpen U := isOpen_interior.inter (hD.preimage hTcont)
  have hzU : z ∈ U := ⟨hzInt, by simpa [hTx] using hx⟩
  have hUΩ : U ⊆ Ω := inter_subset_left.trans (interior_subset.trans hKΩ)
  have hψ_cont1 : ContDiffOn ℝ 1 ψ U := by
    have hT_smooth : ContDiff ℝ 1 T := (contDiff_id.add contDiff_const).sub contDiff_const
    exact (hφ.comp hT_smooth.contDiffOn (fun w hw => hw.2)).sub contDiffOn_const
  have hgradψ (w : Space n) : gradient ψ w = gradient φ (T w) := by
    have heq : ψ = fun u => φ (u + T w - w) + (-d) := by
      funext u; dsimp only [ψ, T]; rw [show u + (w + x - z) - w = u + x - z by abel]; ring
    rw [heq]
    exact BMCompactAnalytic.gradient_diagonal_translate_add_const φ w (T w) (-d)
  have hFψ : ContDiffOn ℝ 1 (fun w => pFlux p (gradient ψ w)) U := by
    have hT_smooth : ContDiff ℝ 1 T := (contDiff_id.add contDiff_const).sub contDiff_const
    have heq : (fun w => pFlux p (gradient ψ w)) = (fun y => pFlux p (gradient φ y)) ∘ T := by
      funext w; simp only [Function.comp_apply, hgradψ]
    rw [heq]
    exact hF.comp hT_smooth.contDiffOn (fun w hw => hw.2)
  have htouchψ : v z = ψ z := by
    dsimp only [ψ, d]; rw [show z + x - z = x by abel]; linarith
  have hstrictψ : ∀ w ∈ U, w ≠ z → ψ w < v w := by
    intro w hwU hwne
    have hTwD : T w ∈ D := hwU.2
    have hTwne : T w ≠ x := by
      intro heq
      apply hwne
      have h0 : w + x - z = z + x - z := heq.trans hTx.symm
      have h1 : w + x = z + x := sub_left_inj.mp h0
      exact add_right_cancel h1
    have hlt := hstrict (T w) hTwD hTwne
    have hle := infConv_le (ε := ε) hK (hvc.mono hKΩ) (T w) (interior_subset hwU.1)
    have hdiff : T w - w = x - z := by dsimp only [T]; abel
    rw [hdiff] at hle
    dsimp only [ψ, d, T] at hlt hle ⊢
    linarith
  have hres := (hv.mono hUΩ hUopen).le_neg_divergence_at_strict_contact (hvc.mono hUΩ) hn hzU
    hψ_cont1 hFψ htouchψ hstrictψ
  -- Identify coordinateDivergence of translated flux at z with original at x
  have hdiv_eq : coordinateDivergence (fun w => pFlux p (gradient ψ w)) z =
      coordinateDivergence (fun y => pFlux p (gradient φ y)) x := by
    unfold coordinateDivergence
    apply Finset.sum_congr rfl
    intro i _
    have heq : (fun w => (pFlux p (gradient ψ w)).ofLp i) =
        fun w => (fun y => (pFlux p (gradient φ y)).ofLp i) (w + x - z) + (0 : ℝ) := by
      funext w; simp [hgradψ, T]
    change (gradient (fun w => (pFlux p (gradient ψ w)).ofLp i) z).ofLp i =
      (gradient (fun y => (pFlux p (gradient φ y)).ofLp i) x).ofLp i
    rw [heq, BMCompactAnalytic.gradient_diagonal_translate_add_const
      (fun y => (pFlux p (gradient φ y)).ofLp i) z x 0]
  rwa [hdiv_eq] at hres

end ViscosityPreservation
end BMCompactPDE
#print axioms BMCompactPDE.supConv_semiconvex_convexOn
#print axioms BMCompactPDE.supConv_semiconvex_lipschitzWith
#print axioms BMCompactPDE.supConv_uniform_close
#print axioms BMCompactPDE.supConv_isViscosityPSubsolution
#print axioms BMCompactPDE.infConv_le_neg_divergence_at_strict_contact
