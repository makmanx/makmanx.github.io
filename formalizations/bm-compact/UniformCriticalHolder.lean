import NextComparisonUniformNaturalRows
import NextComparisonLocalSobolev
import UpstreamGreenUniformMorrey

/-! Quantitative regularity for a family of actual weak solutions at the
critical exponent. A single natural-gradient row estimate on a collar gives
a common higher gradient norm and an interior Hölder estimate. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal NNReal ContDiff BigOperators
namespace BMCompactPDE

private theorem critical_collar {n : ℕ} {Ω D : Set (Space n)} (hΩ : IsOpen Ω)
    (hD : LocalDomain D Ω) : ∃ U, LocalDomain U Ω ∧ LocalDomain D U := by
  have hK : IsCompact (closure D) := hD.2.1.isCompact_closure
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_cthickening_subset_open hΩ hD.2.2
  exact ⟨thickening δ (closure D),
    ⟨isOpen_thickening,hK.isBounded.thickening,(closure_thickening_subset_cthickening _ _).trans hthick⟩,
    hD.1,hD.2.1,self_subset_thickening hδ _⟩

private theorem critical_natural_norm {n : ℕ} {p : ℝ} (hp : 2≤p) (v : Space n) :
    ‖naturalGradientMap p 0 v‖=‖v‖^(p/2) := by
  rw [naturalGradientMap,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  norm_num only [zero_pow,zero_add]
  rw [←Real.rpow_two,←Real.rpow_mul (norm_nonneg v)]
  have he : 2*((p-2)/4)=(p/2+1)-2 := by ring
  rw [he]
  have hh := rpow_coefficient_mul (p:=p/2+1) (by linarith) (norm_nonneg v)
  simpa only [show p/2+1-1=p/2 by ring] using hh

private theorem critical_vector_bound {n : ℕ} {μ : Measure (Space n)} {s : ℝ≥0∞}
    {F : Space n → Space n} {M : ℝ} (hs : 1≤s) (hM : 0≤M)
    (hm : ∀ i, MemLp (fun x => F x i) s μ)
    (hb : ∀ i, (eLpNorm (fun x => F x i) s μ).toReal≤M) :
    (eLpNorm F s μ).toReal ≤ (n:ℝ)*M := by
  classical
  let f : Fin n → Space n → ℝ := fun i x => ‖F x i‖
  have hpoint (x : Space n) : ‖F x‖≤‖(∑ i, f i) x‖ := by
    rw [Finset.sum_apply,Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mp
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)
  apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Nat.cast_nonneg _) hM)
  calc
    _ ≤ eLpNorm (∑ i, f i) s μ := eLpNorm_mono_ae (Eventually.of_forall hpoint)
    _ ≤ ∑ i, eLpNorm (f i) s μ := eLpNorm_sum_le (fun i _ => (hm i).norm.1) hs
    _ ≤ ∑ _ : Fin n, ENNReal.ofReal M := by
      apply Finset.sum_le_sum
      intro i _
      change eLpNorm (fun x => ‖F x i‖) s μ ≤ _
      rw [eLpNorm_norm]
      exact (ENNReal.le_ofReal_iff_toReal_le (hm i).eLpNorm_ne_top hM).mpr (hb i)
    _ = _ := by simp [ENNReal.ofReal_mul, Nat.cast_nonneg]

private theorem critical_lower_norm {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {μ : Measure (Space n)} [IsFiniteMeasure μ] {r : ℝ} (hr : 0<r) (hr2 : r≤2)
    {f : Space n → E} (hf : MemLp f 2 μ) :
    (eLpNorm f (ENNReal.ofReal r) μ).toReal ≤
      (eLpNorm f 2 μ).toReal * (μ univ ^ (1/r-1/2 : ℝ)).toReal := by
  have hle : ENNReal.ofReal r ≤ 2 := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hr2
  have he : 0 ≤ 1/r-1/2 := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le hr hr2
  have hh := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hle hf.1
  simp only [ENNReal.toReal_ofReal hr.le,ENNReal.toReal_ofNat] at hh
  have hfin := ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top μ univ)
  simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_ne_top hfin) hh

private theorem critical_power_norm {n : ℕ} {μ : Measure (Space n)} {p s : ℝ}
    (hp : 2≤p) (hs : 0≤s) (g : Space n → Space n) :
    (eLpNorm (fun x => naturalGradientMap p 0 (g x)) (ENNReal.ofReal s) μ).toReal =
    (eLpNorm g (ENNReal.ofReal (s*(p/2))) μ).toReal ^ (p/2) := by
  have hhalf : 0<p/2 := by linarith
  rw [← eLpNorm_norm (fun x => naturalGradientMap p 0 (g x))]
  simp only [critical_natural_norm hp,eLpNorm_norm_rpow g hhalf,← ENNReal.ofReal_mul hs,
    ← ENNReal.toReal_rpow]

set_option maxHeartbeats 1400000 in
/-- A family with common actual critical Sobolev ceilings has one interior
gradient ceiling strictly above the dimension. No higher norm is supplied. -/
theorem exists_uniform_critical_gradient_gain_of_weak_source_family
    {n : ℕ} {c : ℝ} {Ω D : Set (Space n)} {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n}
    (hH : ∀ j, WeakPSourcePair (n:ℝ) c Ω (u j) (g j))
    (hf : ∀ j, SobolevPair (n:ℝ) Ω (u j) (g j))
    (hn : 2≤n) (hΩb : Bornology.IsBounded Ω) {U N : ℝ} (hU : 0≤U) (hN : 0≤N)
    (hNu : ∀ j, (eLpNorm (u j) (ENNReal.ofReal n) (volume.restrict Ω)).toReal≤U)
    (hNg : ∀ j, (eLpNorm (g j) (ENNReal.ofReal n) (volume.restrict Ω)).toReal≤N)
    (hD : LocalDomain D Ω) :
    ∃ A : ℝ, 0≤A ∧ ∀ j,
      MemLp (g j) (ENNReal.ofReal ((n:ℝ)^2/((n:ℝ)-1))) (volume.restrict D) ∧
      (eLpNorm (g j) (ENNReal.ofReal ((n:ℝ)^2/((n:ℝ)-1))) (volume.restrict D)).toReal≤A := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hd : (0:ℝ)<n-1 := by linarith
  have hp2 : 0<(n:ℝ)/2 := by linarith
  let r := 2*(n:ℝ)/((n:ℝ)+1)
  let s := 2*(n:ℝ)/((n:ℝ)-1)
  let q := (n:ℝ)^2/((n:ℝ)-1)
  have hden : 0<(n:ℝ)+1 := by linarith
  have hr : 1<r := (lt_div_iff₀ hden).mpr (by linarith)
  have hr2 : r<2 := (div_lt_iff₀ hden).mpr (by linarith)
  have hrn := hr2.trans_le hnR
  have hs : 1<s := (lt_div_iff₀ hd).mpr (by linarith)
  have hsr : (n:ℝ)*r/(n-r)=s := by
    apply (div_eq_iff (sub_ne_zero.mpr hrn.ne')).mpr
    dsimp only [r,s]
    field_simp [hden.ne',hd.ne']
    <;> ring
  have hq : s*((n:ℝ)/2)=q := by dsimp only [s,q]; ring
  obtain ⟨W,hW,hDW⟩ := critical_collar (hH 0).2.1 hD
  let μ := volume.restrict W
  let ν := volume.restrict D
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hW.2.1.measure_lt_top.ne
  let d := (μ univ ^ (1/r-1/2:ℝ)).toReal
  obtain ⟨M,hM,hrows⟩ := exists_uniform_naturalGradient_sobolev_rows_of_weak_source_family hH hf hnR hn hΩb hU hN hNu hNg hW
  obtain ⟨S,hS,hSob⟩ := exists_local_sobolev_norm_coefficient hr hrn hW.1 hDW
  rw [hsr] at hSob
  let L := S*(N^((n:ℝ)/2)*d+((n:ℝ)*M)*d)
  have hL : 0≤L := mul_nonneg hS (add_nonneg (mul_nonneg (Real.rpow_nonneg hN _) ENNReal.toReal_nonneg)
    (mul_nonneg (mul_nonneg hn0.le hM) ENNReal.toReal_nonneg))
  refine ⟨((n:ℝ)*L)^((n:ℝ)/2)⁻¹,Real.rpow_nonneg (mul_nonneg hn0.le hL) _,?_⟩
  intro j
  let V : Space n → Space n := fun x => naturalGradientMap (n:ℝ) 0 (g j x)
  obtain ⟨H,hHrow,hHb⟩ := hrows j
  have hgW := (hf j).2.2.1.mono_measure (Measure.restrict_mono_set volume (subset_closure.trans hW.2.2))
  have hgWN : (eLpNorm (g j) (ENNReal.ofReal n) μ).toReal≤N :=
    (ENNReal.toReal_mono (hf j).2.2.1.eLpNorm_ne_top (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume (subset_closure.trans hW.2.2)))).trans (hNg j)
  have hVN : (eLpNorm V 2 μ).toReal≤N^((n:ℝ)/2) := by
    have he := critical_power_norm (μ:=μ) hnR (by norm_num : (0:ℝ)≤2) (g j)
    rw [show 2*((n:ℝ)/2)=(n:ℝ) by ring] at he
    have he2 : (eLpNorm V 2 μ).toReal = (eLpNorm (g j) (ENNReal.ofReal n) μ).toReal ^ ((n:ℝ)/2) := by
      simpa only [ENNReal.ofReal_ofNat] using he
    exact he2.le.trans (Real.rpow_le_rpow ENNReal.toReal_nonneg hgWN hp2.le)
  have hcmp (i : Fin n) : (eLpNorm (fun x => V x i) 2 μ).toReal≤N^((n:ℝ)/2) := by
    exact (ENNReal.toReal_mono (memLp_naturalGradientMap (ε:=0) hnR hgW).eLpNorm_ne_top
      (eLpNorm_mono_ae (Eventually.of_forall (fun x => PiLp.norm_apply_le (V x) i)))).trans hVN
  have hres (i : Fin n) : MemLp (fun x => V x i) (ENNReal.ofReal s) ν ∧
      (eLpNorm (fun x => V x i) (ENNReal.ofReal s) ν).toReal ≤ L := by
    have hs0 := hHrow i
    have hHm : MemLp (H i) 2 μ := by simpa only [ENNReal.ofReal_ofNat] using hs0.2.2.1
    have hB : (eLpNorm (H i) 2 μ).toReal≤(n:ℝ)*M :=
      critical_vector_bound (by norm_num) hM (memLp_piLp_iff.mp hHm) (hHb i)
    have hle := ENNReal.ofReal_le_ofReal hr2.le
    have hs1 : SobolevPair r W (fun x => V x i) (H i) :=
      ⟨hr,hs0.2.1.mono_exponent hle,hs0.2.2.1.mono_exponent hle,hs0.2.2.2⟩
    obtain ⟨hm,hb⟩ := hSob _ _ hs1
    refine ⟨hm,hb.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hS)⟩
    · exact (critical_lower_norm (zero_lt_one.trans hr) hr2.le (by simpa only [ENNReal.ofReal_ofNat] using hs0.2.1)).trans
        (mul_le_mul_of_nonneg_right (hcmp i) ENNReal.toReal_nonneg)
    · exact (critical_lower_norm (zero_lt_one.trans hr) hr2.le (by simpa only [ENNReal.ofReal_ofNat] using hs0.2.2.1)).trans
        (mul_le_mul_of_nonneg_right hB ENNReal.toReal_nonneg)
  have hvm : MemLp V (ENNReal.ofReal s) ν := memLp_piLp_iff.mpr (fun i => (hres i).1)
  have hvb := critical_vector_bound (ENNReal.one_le_ofReal.mpr hs.le) hL
    (fun i => (hres i).1) (fun i => (hres i).2)
  have hnorm := critical_power_norm (μ:=ν) hnR (zero_lt_one.trans hs).le (g j)
  rw [hq] at hnorm
  have he : ENNReal.ofReal q / ENNReal.ofReal ((n:ℝ)/2)=ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_div_of_pos hp2, ← hq, mul_div_cancel_right₀ _ hp2.ne']
  constructor
  · apply (memLp_norm_rpow_iff (p:=ENNReal.ofReal q) (q:=ENNReal.ofReal ((n:ℝ)/2))
      ((hH j).2.2.1 D hD).2.2.1.1 (ENNReal.ofReal_ne_zero_iff.mpr hp2) ENNReal.ofReal_ne_top).mp
    simpa only [he,ENNReal.toReal_ofReal hp2.le,V,critical_natural_norm hnR] using! hvm.norm
  · exact (Real.le_rpow_inv_iff_of_pos ENNReal.toReal_nonneg (mul_nonneg hn0.le hL) hp2).mpr
      (hnorm.symm.le.trans hvb)

/-- On each compactly contained open subdomain a critical weak-source
family with common scalar and natural energy bounds has a common Hölder
constant. The exponent is uniform in all dimensions, including the plane. -/
theorem exists_uniform_critical_holder_of_weak_source_family
    {n : ℕ} {c : ℝ} {Ω D : Set (Space n)} {u : ℕ → Space n → ℝ} {g : ℕ → Space n → Space n}
    (hH : ∀ j, WeakPSourcePair (n:ℝ) c Ω (u j) (g j))
    (hf : ∀ j, SobolevPair (n:ℝ) Ω (u j) (g j))
    (hn : 2≤n) (hΩb : Bornology.IsBounded Ω) {U N : ℝ} (hU : 0≤U) (hN : 0≤N)
    (hNu : ∀ j, (eLpNorm (u j) (ENNReal.ofReal n) (volume.restrict Ω)).toReal≤U)
    (hNg : ∀ j, (eLpNorm (g j) (ENNReal.ofReal n) (volume.restrict Ω)).toReal≤N)
    (hcont : ∀ j, ContinuousOn (u j) Ω) {B : ℝ} (hB : 0≤B)
    (hpoint : ∀ j x, x∈Ω → ‖u j x‖≤B) (hD : LocalDomain D Ω) :
    ∃ C : ℝ, 0≤C ∧ ∀ j x, x∈closure D → ∀ y, y∈closure D →
      dist (u j x) (u j y) ≤ C * dist x y ^ (1/(n:ℝ)) := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by linarith
  have hd : (0:ℝ)<n-1 := by linarith
  let q := (n:ℝ)^2/((n:ℝ)-1)
  have hnq : (n:ℝ)<q := (lt_div_iff₀ hd).mpr (by nlinarith)
  have hq : 1<q := lt_trans (by linarith) hnq
  have he : 1-(n:ℝ)/q=1/(n:ℝ) := by
    dsimp only [q]
    field_simp [hn0.ne',hd.ne']
    <;> ring
  obtain ⟨W,hW,hDW⟩ := critical_collar (hH 0).2.1 hD
  have hWΩ := subset_closure.trans hW.2.2
  obtain ⟨A,hA,hgain⟩ := exists_uniform_critical_gradient_gain_of_weak_source_family hH hf hn hΩb hU hN hNu hNg hW
  let μ := volume.restrict W
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hW.2.1.measure_lt_top.ne
  let Q := ENNReal.ofReal q
  have hconst : MemLp (fun _ : Space n => B) Q μ := memLp_const B
  let T := (eLpNorm (fun _ : Space n => B) Q μ).toReal
  have hdom (j : ℕ) : ∀ᵐ x ∂μ, ‖u j x‖≤‖B‖ := by
    filter_upwards [ae_restrict_mem hW.1.measurableSet] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg hB] using hpoint j x (hWΩ hx)
  have hsob (j : ℕ) : SobolevPair q W (u j) (g j) := by
    have hw := (hf j).mono_actual hWΩ
    refine ⟨hq, hconst.of_le hw.2.1.1 (hdom j), (hgain j).1, hw.2.2.2⟩
  obtain ⟨K,hK,hMorrey⟩ := exists_uniform_local_morrey_coefficient_for_continuous_sobolev_families
    (ι:=ℕ) (by omega : 1≤n) hnq hW.1 hDW
  refine ⟨K*(T+A),mul_nonneg hK (add_nonneg ENNReal.toReal_nonneg hA),?_⟩
  simpa only [he] using hMorrey T A ENNReal.toReal_nonneg hA u g hsob
    (fun j => (hcont j).mono hWΩ)
    (fun j => ENNReal.toReal_mono hconst.eLpNorm_ne_top (eLpNorm_mono_ae (hdom j)))
    (fun j => (hgain j).2)

end BMCompactPDE
#print axioms BMCompactPDE.exists_uniform_critical_gradient_gain_of_weak_source_family

#print axioms BMCompactPDE.exists_uniform_critical_holder_of_weak_source_family
