import CapacityFoundation

/-! Outer-neighborhood infimum identity for the literal smooth variational
capacity. This does not identify that variational definition on open sets with
the separately inner-regularized open-set capacity in the manuscript. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace BMCompactCapacityV2

theorem le_of_forall_scaled_energy {a b : ℝ≥0∞} (p : ℝ) (hp : 0 < p)
    (hb : b ≠ ⊤) (h : ∀ c : ℝ, 1 < c → a ≤ ENNReal.ofReal (c ^ p) * b) :
    a ≤ b := by
  have hpow : Continuous (fun c : ℝ => c ^ p) :=
    continuous_id.rpow_const (fun _ => Or.inr hp.le)
  have hcont : Continuous (fun c : ℝ => ENNReal.ofReal (c ^ p) * b) :=
    (ENNReal.continuous_mul_const hb).comp (ENNReal.continuous_ofReal.comp hpow)
  have ht : Tendsto (fun c : ℝ => ENNReal.ofReal (c ^ p) * b)
      (𝓝[>] (1 : ℝ)) (𝓝 b) := by
    simpa using (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact h c hc

def openEnlargementInf {n : ℕ} (p : ℝ) (K O : Set (Space n)) : ℝ≥0∞ :=
  ⨅ (U : Set (Space n)) (_ : IsOpen U) (_ : K ⊆ U) (_ : U ⊆ O),
    relativeCapacity p U O

theorem relativeCapacity_le_openEnlargementInf {n : ℕ} (p : ℝ)
    (K O : Set (Space n)) : relativeCapacity p K O ≤ openEnlargementInf p K O := by
  apply le_iInf
  intro U
  apply le_iInf
  intro hU
  apply le_iInf
  intro hKU
  apply le_iInf
  intro hUO
  exact relativeCapacity_mono p hKU

theorem relativeCapacity_eq_openEnlargementInf {n : ℕ} (p : ℝ) (hp : 0 < p)
    (K O : Set (Space n)) : relativeCapacity p K O = openEnlargementInf p K O := by
  apply le_antisymm (relativeCapacity_le_openEnlargementInf p K O)
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  apply le_of_forall_scaled_energy p hp
    (pEnergy_ne_top_of_smooth_compactSupport p hp O hf.1 hf.2.1)
  intro c hc
  obtain ⟨U, hU, hKU, hUO, hUE⟩ := exists_open_capacity_le_scaled_energy p hf hc
  have hinf : openEnlargementInf p K O ≤ relativeCapacity p U O :=
    iInf_le_of_le U (iInf_le_of_le hU (iInf_le_of_le hKU (iInf_le_of_le hUO le_rfl)))
  simpa only [abs_of_pos (zero_lt_one.trans hc)] using hinf.trans hUE

end BMCompactCapacityV2

#print axioms BMCompactCapacityV2.le_of_forall_scaled_energy
#print axioms BMCompactCapacityV2.relativeCapacity_le_openEnlargementInf
#print axioms BMCompactCapacityV2.relativeCapacity_eq_openEnlargementInf
