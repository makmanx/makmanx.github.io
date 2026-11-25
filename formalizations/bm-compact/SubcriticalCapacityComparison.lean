import SubcriticalNeighborhoodFarField
import CapacityNormalizationFull

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Bornology BMCompactCapacityV2
open scoped Topology ENNReal Pointwise
namespace BMCompactPDE

/-- The only substantive premise is the diagonal comparison of independently
constructed neighborhood potentials. No asymptotic, capacity or Green comparison
is posited. The conclusion is the full inequality with the paper's variational capacity. -/
theorem theoremA_subcritical_of_diagonal_comparison {n : ℕ} {p : ℝ} (hp : 1<p) (hpn : p<(n:ℝ))
    (hcmp : ∀ {K L : Set (Space n)}, IsCompact K → IsCompact L → K.Nonempty → L.Nonempty →
      ∀ {s : ℝ}, 0<s → s<1 → ∀ {δ : ℝ}, 0<δ →
      ∀ (u : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood δ K))
        (v : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood δ L))
        (w : ContinuousUnitCapacityData p (BMCompact.closedNeighborhood δ (s • K+(1-s) • L))),
        ∀ x, min (u.scalar x) (v.scalar x) ≤ w.scalar x)
    {E F : Set (Space n)} (hE : IsCompact E) (hF : IsCompact F) (he : E.Nonempty) (hf : F.Nonempty)
    {t : ℝ} (ht : 0≤t) (ht1 : t≤1) :
    ENNReal.ofReal t*variationalCapacity p E^(1/((n:ℝ)-p)) +
      ENNReal.ofReal (1-t)*variationalCapacity p F^(1/((n:ℝ)-p)) ≤
        variationalCapacity p (t • E+(1-t) • F)^(1/((n:ℝ)-p)) := by
  have hn1 : 1<n := by exact_mod_cast hp.trans hpn
  have hp0 := zero_lt_one.trans hp
  let _ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  apply subcritical_ENNReal_BM_of_min_comparison p hp0 hpn _ E F hE hF he hf t ht ht1
  intro K L hK hL hk hl s hs hs1
  let M := s • K+(1-s) • L
  have hM : IsCompact M := (hK.smul _).add (hL.smul _)
  have hm : M.Nonempty := (hk.image _).add (hl.image _)
  have hcap : min (variationalCapacity p K) (variationalCapacity p L) ≤ variationalCapacity p M := by
    apply le_of_tendsto_of_tendsto ((tendsto_variationalCapacity_cthickening p hp0 hK).min
      (tendsto_variationalCapacity_cthickening p hp0 hL)) (tendsto_variationalCapacity_cthickening p hp0 hM)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    let r : Ioi (0:ℝ) := ⟨δ,hδ⟩
    obtain ⟨U,_⟩ := exists_subcritical_outer_neighborhood_potential hp hpn hK
    obtain ⟨V,_⟩ := exists_subcritical_outer_neighborhood_potential hp hpn hL
    obtain ⟨W,_⟩ := exists_subcritical_outer_neighborhood_potential hp hpn hM
    obtain ⟨a,ha,la,ea⟩ := (U r).subcritical_neighborhood_far_field hp hpn hK hk hδ
    obtain ⟨b,hb,lb,eb⟩ := (V r).subcritical_neighborhood_far_field hp hpn hL hl hδ
    obtain ⟨c,hc,lc,ec⟩ := (W r).subcritical_neighborhood_far_field hp hpn hM hm hδ
    have hh := le_of_tendsto_of_tendsto' (la.min lb) lc (fun x => by
      rw [← mul_min_of_nonneg _ _ (Real.rpow_nonneg (norm_nonneg _) _)]
      exact mul_le_mul_of_nonneg_left (hcmp hK hL hk hl hs hs1 hδ (U r) (V r) (W r) x)
        (Real.rpow_nonneg (norm_nonneg _) _))
    let factor := (((n:ℝ)-p)/(p-1))^(p-1)
    have hfac : 0≤factor := Real.rpow_nonneg (div_pos (sub_pos.mpr hpn) (sub_pos.mpr hp)).le _
    have hσ : 0≤canonicalSphereArea n := (canonicalSphereArea_pos (by omega)).le
    have hmono {u v : ℝ} (hu : 0<u) (h : u≤v) :
        u^(p-1)*factor*canonicalSphereArea n ≤ v^(p-1)*factor*canonicalSphereArea n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hu.le h (sub_pos.mpr hp).le) hfac) hσ
    have H {S : Set (Space n)} (hS : IsCompact S) {d : ℝ} (hd : 0<d) (h : d≤c)
        (hz : d^(p-1)*factor*canonicalSphereArea n=(variationalCapacity p S).toReal) :
        variationalCapacity p S ≤ variationalCapacity p (BMCompact.closedNeighborhood δ M) := by
      have h' := hmono hd h
      change _ ≤ c^(p-1)*(((n:ℝ)-p)/(p-1))^(p-1)*canonicalSphereArea n at h'
      rw [hz,ec] at h'
      exact (ENNReal.toReal_le_toReal (variationalCapacity_ne_top_of_isCompact p hp0 hS)
        (variationalCapacity_ne_top_of_isCompact p hp0 (BMCompact.isCompact_closedNeighborhood hM δ))).mp h'
    rcases le_total a b with hab|hab
    · exact (min_le_left _ _).trans (H (BMCompact.isCompact_closedNeighborhood hK δ) ha
        ((min_eq_left hab) ▸ hh) ea)
    · exact (min_le_right _ _).trans (H (BMCompact.isCompact_closedNeighborhood hL δ) hb
        ((min_eq_right hab) ▸ hh) eb)
  have hex : 0≤1/((n:ℝ)-p) := (one_div_pos.mpr (sub_pos.mpr hpn)).le
  have transcap {S : Set (Space n)} (h : variationalCapacity p S≤variationalCapacity p M) :
      subcriticalCapacityRoot p S≤subcriticalCapacityRoot p M :=
    ENNReal.toReal_mono (ENNReal.rpow_ne_top_of_nonneg hex (variationalCapacity_ne_top_of_isCompact p hp0 hM))
      (ENNReal.rpow_le_rpow h hex)
  rcases le_total (variationalCapacity p K) (variationalCapacity p L) with h | h
  · rw [min_eq_left h] at hcap
    exact (min_le_left _ _).trans (transcap hcap)
  · rw [min_eq_right h] at hcap
    exact (min_le_right _ _).trans (transcap hcap)

end BMCompactPDE
#print axioms BMCompactPDE.theoremA_subcritical_of_diagonal_comparison
