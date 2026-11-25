import WeakEnergyUniqueness
import CapacityFoundation
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
A genuine bounded-domain Poincare consequence for the explicit zero-boundary
Sobolev graph. The smooth compact-support inequality is derived from Mathlib's
proved Gagliardo-Nirenberg-Sobolev inequality at exponent one, rather than
assumed. Finite-measure Holder comparison transfers both graph limits to L1.
The resulting zero-gradient criterion gives function-level weak Dirichlet
uniqueness under an actual zero-boundary difference.
-/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology ContDiff

namespace BMCompactPDE

/-- On a finite-measure domain, convergence to zero of an Lp seminorm (p>1)
implies convergence to zero in L1, by the actual finite-measure Holder bound. -/
theorem tendsto_eLpNorm_one_of_tendsto_eLpNorm_ofReal
    {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ} (hp : 1 < p)
    {f : ℕ → α → F} (hf : ∀ j, AEStronglyMeasurable (f j) μ)
    (hlim : Tendsto (fun j => eLpNorm (f j) (ENNReal.ofReal p) μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (f j) 1 μ) atTop (𝓝 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  let C : ℝ≥0∞ := μ univ ^ (1 - 1 / p)
  have he : 0 ≤ 1 - 1 / p := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hp0).2 (by simpa using hp.le)
  have hC : C ≠ (∞ : ℝ≥0∞) :=
    ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top μ univ)
  have hbound (j : ℕ) : eLpNorm (f j) 1 μ ≤ eLpNorm (f j) (ENNReal.ofReal p) μ * C := by
    simpa only [ENNReal.toReal_one, ENNReal.toReal_ofReal hp0.le, div_one] using
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hle (hf j)
  have hupper : Tendsto (fun j => eLpNorm (f j) (ENNReal.ofReal p) μ * C)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hlim (Or.inr hC)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper (fun _ => bot_le) hbound

/-- A finite, uniform L1 Poincare constant for every genuine smooth compact
support test in a bounded Euclidean domain of dimension at least two. -/
theorem exists_L1_poincare_constant {n : ℕ} (hn : 2 ≤ n)
    {D : Set (Space n)} (hDb : Bornology.IsBounded D) :
    ∃ C : ℝ≥0, ∀ φ : Space n → ℝ, SmoothTest D φ →
      eLpNorm φ 1 (volume.restrict D) ≤ C * eLpNorm (gradient φ) 1 (volume.restrict D) := by
  let C : ℝ≥0 := eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure (Space n)) D 1 1
  refine ⟨C, ?_⟩
  intro φ hφ
  have hsupport : Function.support φ ⊆ D := (subset_tsupport φ).trans hφ.2.2
  have hgradSupport : Function.support (gradient φ) ⊆ D := by
    intro x hx
    by_contra hxD
    have hxφ : x ∉ tsupport φ := fun ht => hxD (hφ.2.2 ht)
    exact hx (BMCompactCapacityV2.gradient_eq_zero_of_notMem_tsupport hxφ)
  have hdim : (1 : ℝ≥0) < Module.finrank ℝ (Space n) := by
    have hn' : 1 < n := Nat.lt_of_lt_of_le (by decide) hn
    simpa only [Space, finrank_euclideanSpace, Fintype.card_fin] using
      (show (1 : ℝ≥0) < (n : ℝ≥0) by exact_mod_cast hn')
  have hineq := eLpNorm_le_eLpNorm_fderiv (volume : Measure (Space n))
    (hφ.1.of_le (by simp) : ContDiff ℝ 1 φ) hsupport
    (p := (1 : ℝ≥0)) le_rfl hdim hDb
  have hnorm : eLpNorm (fderiv ℝ φ) 1 (volume : Measure (Space n)) =
      eLpNorm (gradient φ) 1 volume := by
    apply eLpNorm_congr_norm_ae
    exact Eventually.of_forall (fun x => by
      simpa only [gradient] using
        ((InnerProductSpace.toDual ℝ (Space n)).symm.norm_map (fderiv ℝ φ x)).symm)
  simp only [ENNReal.coe_one] at hineq
  rw [hnorm] at hineq
  simpa only [ENNReal.coe_one, eLpNorm_restrict_eq_of_support_subset hsupport,
    eLpNorm_restrict_eq_of_support_subset hgradSupport] using hineq

/-- Zero weak gradient and genuine zero boundary values force the Sobolev
function to vanish a.e.; no free Poincare hypothesis is introduced. -/
theorem ZeroBoundarySobolevPair.ae_eq_zero_of_gradient_ae_zero
    {n : ℕ} {p : ℝ} {D : Set (Space n)} {u : Space n → ℝ}
    {g : Space n → Space n} (hu : ZeroBoundarySobolevPair p D u g)
    (hn : 2 ≤ n) (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    (hg : g =ᵐ[volume.restrict D] 0) : u =ᵐ[volume.restrict D] 0 := by
  obtain ⟨hSob, φ, hφ, hfunlim, hgradlim⟩ := hu
  haveI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hDb.measure_lt_top.ne
  have hφmem (j : ℕ) : MemLp (φ j) (ENNReal.ofReal p) (volume.restrict D) :=
    (BMCompactCapacityV2.smooth_compactSupport_memLp
      (ENNReal.ofReal p) (hφ j).1 (hφ j).2.1).restrict D
  have hgradmem (j : ℕ) : MemLp (gradient (φ j)) (ENNReal.ofReal p) (volume.restrict D) :=
    (BMCompactCapacityV2.gradient_smooth_compactSupport_memLp
      (ENNReal.ofReal p) (hφ j).1 (hφ j).2.1).restrict D
  have hfun1 := tendsto_eLpNorm_one_of_tendsto_eLpNorm_ofReal hSob.1
    (fun j => (hφmem j).1.sub hSob.2.1.1) hfunlim
  have hgrad1diff := tendsto_eLpNorm_one_of_tendsto_eLpNorm_ofReal hSob.1
    (fun j => (hgradmem j).1.sub hSob.2.2.1.1) hgradlim
  have hgrad1 : Tendsto (fun j => eLpNorm (gradient (φ j)) 1 (volume.restrict D))
      atTop (𝓝 0) := by
    convert hgrad1diff using 1
    funext j
    apply eLpNorm_congr_ae
    filter_upwards [hg] with x hx
    simp only [Pi.sub_apply, hx, Pi.zero_apply, sub_zero]
  obtain ⟨C, hC⟩ := exists_L1_poincare_constant hn hDb
  have hφ1 : Tendsto (fun j => eLpNorm (φ j) 1 (volume.restrict D)) atTop (𝓝 0) := by
    have hupper : Tendsto (fun j => (C : ℝ≥0∞) * eLpNorm (gradient (φ j)) 1
        (volume.restrict D)) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hgrad1
        (Or.inr ENNReal.coe_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hupper (fun _ => bot_le) (fun j => hC (φ j) (hφ j))
  have hbound (j : ℕ) : eLpNorm u 1 (volume.restrict D) ≤
      eLpNorm (φ j - u) 1 (volume.restrict D) + eLpNorm (φ j) 1 (volume.restrict D) := by
    have hb := eLpNorm_add_le (hSob.2.1.1.sub (hφmem j).1) (hφmem j).1
      (by rfl : (1 : ℝ≥0∞) ≤ 1)
    have heq : u - φ j + φ j = u := sub_add_cancel u (φ j)
    rw [heq] at hb
    simpa only [eLpNorm_sub_comm] using hb
  have hu0 : eLpNorm u 1 (volume.restrict D) = 0 := by
    apply le_antisymm _ bot_le
    have hsum : Tendsto (fun j => eLpNorm (φ j - u) 1 (volume.restrict D) +
        eLpNorm (φ j) 1 (volume.restrict D)) atTop (𝓝 0) := by
      simpa only [add_zero] using hfun1.add hφ1
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hsum (Eventually.of_forall hbound)
  exact (eLpNorm_eq_zero_iff hSob.2.1.1 one_ne_zero).1 hu0

/-- Function-level weak Dirichlet uniqueness on a bounded relatively compact
subdomain, when the difference is in the actual zero-boundary Sobolev graph. -/
theorem WeakPHarmonicPair.ae_eq_of_zeroBoundaryDifference
    {n : ℕ} {p : ℝ} {Ω D : Set (Space n)}
    {u v : Space n → ℝ} {g h : Space n → Space n}
    (hu : WeakPHarmonicPair p Ω u g) (hv : WeakPHarmonicPair p Ω v h)
    (hn : 2 ≤ n) (hD : LocalDomain D Ω)
    (hboundary : ZeroBoundarySobolevPair p D (u - v) (g - h)) :
    u =ᵐ[volume.restrict D] v := by
  have hgrad := hu.gradient_ae_eq_of_zeroBoundaryDifference hv hD hboundary
  have hdiff : (g - h) =ᵐ[volume.restrict D] 0 := by
    filter_upwards [hgrad] with x hx
    simp only [Pi.sub_apply, hx, sub_self, Pi.zero_apply]
  have hzero := hboundary.ae_eq_zero_of_gradient_ae_zero hn hD.1 hD.2.1 hdiff
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

end BMCompactPDE

#print axioms BMCompactPDE.tendsto_eLpNorm_one_of_tendsto_eLpNorm_ofReal
#print axioms BMCompactPDE.exists_L1_poincare_constant
#print axioms BMCompactPDE.ZeroBoundarySobolevPair.ae_eq_zero_of_gradient_ae_zero
#print axioms BMCompactPDE.WeakPHarmonicPair.ae_eq_of_zeroBoundaryDifference
