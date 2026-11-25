import ContinuousOscillationDrop
import RootDilationBatch

/-! The actual normalized source-PDE oscillation alternative at arbitrary
centers/radii/intervals. Both the PDE source and a.e. volume bounds are changed
by the genuine affine maps; no spatial regularity premise is supplied. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric
open scoped Topology ENNReal
namespace BMCompactPDE

theorem continuous_ae_affine_ball_iff {n : ℕ} (a : Space n) {R : ℝ} (hR : 0<R)
    (r : ℝ) (P : Space n → Prop) :
    (∀ᵐ x ∂volume.restrict (ball (0 : Space n) r),P (a+R • x)) ↔
      ∀ᵐ y ∂volume.restrict (ball a (R*r)),P y := by
  let T : Space n ≃ₜ Space n :=
    (Homeomorph.smul (Units.mk0 R hR.ne')).trans (Homeomorph.addLeft a)
  let J : ℝ≥0∞ := spatialDilationJacobian n R
  have hJ : J≠0 := by
    dsimp only [J,spatialDilationJacobian]
    exact ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr (inv_ne_zero (pow_ne_zero n hR.ne')))
  have hS : MeasurePreserving (fun x : Space n => R • x) volume (J • volume) := by
    simpa only [J,preimage_univ,Measure.restrict_univ] using
      measurePreserving_dilation_restrict (n:=n) MeasurableSet.univ hR.ne'
  have hA := (measurePreserving_add_left (volume : Measure (Space n)) a).smul_measure J
  have hT : MeasurePreserving T volume (J • volume) := hA.comp hS
  have hpre : T ⁻¹' ball a (R*r)=ball (0 : Space n) r := by
    ext x
    change dist (a+R • x) a<R*r ↔ dist x 0<r
    simp only [dist_eq_norm,add_sub_cancel_left,sub_zero,norm_smul,
      Real.norm_eq_abs,abs_of_pos hR]
    exact mul_lt_mul_iff_right₀ hR
  have hTB := hT.restrict_preimage (s:=ball a (R*r)) measurableSet_ball
  rw [hpre,Measure.restrict_smul] at hTB
  have hi : (∀ᵐ x ∂volume.restrict (ball (0 : Space n) r),P (T x)) ↔
      ∀ᵐ y ∂J • volume.restrict (ball a (R*r)),P y := by
    rw [←hTB.map_eq]
    exact T.measurableEmbedding.ae_map_iff.symm
  exact hi.trans (Measure.ae_ennreal_smul_measure_iff hJ)

private theorem continuous_source_pair_affine_positive {n : ℕ} {p c a : ℝ}
    {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPSourcePair p c Ω u g) (ha : 0<a) (b : ℝ) :
    WeakPSourcePair p (a^(p-1)*c) Ω (fun x => a*(u x-b)) (a • g) := by
  refine ⟨hu.1,hu.2.1,?_,?_⟩
  · intro D hD
    have hs := ((hu.2.2.1.add_const hu.1 (-b)) D hD).smul a
    apply hs.congr
    · exact Eventually.of_forall (fun x => by simp only [Pi.smul_apply,smul_eq_mul,sub_eq_add_neg])
    · exact Eventually.of_forall (fun _ => rfl)
  · intro D hD θ h hθ
    obtain ⟨hi,he⟩ := hu.2.2.2 D hD θ h hθ
    have hscale : fluxPairing p (a • g) h=fun x => a^(p-1)*fluxPairing p g h x := by
      funext x
      simp only [fluxPairing,Pi.smul_apply,pFlux_nonneg_smul hu.1 ha.le,real_inner_smul_left]
    rw [hscale]
    refine ⟨hi.const_mul _,?_⟩
    rw [integral_const_mul,he,mul_assoc]

theorem exists_source_spatial_oscillation_alternative {n : ℕ} {p : ℝ}
    (hp : 1<p) (hpn : p<(n : ℝ)) :
    ∃ δ : ℝ,0<δ ∧ δ<1/2 ∧ ∃ ε₀ : ℝ,0<ε₀ ∧
      ∀ {c : ℝ} {Ω : Set (Space n)} {u : Space n → ℝ} {g : Space n → Space n},
        WeakPSourcePair p c Ω u g → ∀ (a : Space n) (R m M : ℝ),0<R → m<M →
        LocalDomain (ball a (R*(3*((n : ℝ)+1)))) Ω →
        (∀ᵐ x ∂volume.restrict (ball a (R*(3*((n : ℝ)+1)))),m≤u x∧u x≤M) →
        R^p*|c| ≤ε₀*(M-m)^(p-1) →
        (∀ᵐ x ∂volume.restrict (ball a (R/4)),u x≤M-δ*(M-m)) ∨
          (∀ᵐ x ∂volume.restrict (ball a (R/4)),m+δ*(M-m)≤u x) := by
  obtain ⟨δ,hδ,hδhalf,ε₀,hε₀,hunit⟩ := exists_unit_source_oscillation_alternative hp hpn
  refine ⟨δ,hδ,hδhalf,ε₀,hε₀,?_⟩
  intro c Ω u g hu a R m M hR hmM hD hbound hsource
  let K : ℝ := 3*((n : ℝ)+1)
  let T : Space n → Space n := fun x => a+R • x
  let Ω' := T ⁻¹' Ω
  let ω : ℝ := M-m
  let A : ℝ := ω⁻¹
  have hω : 0<ω := sub_pos.mpr hmM
  have hA : 0<A := inv_pos.mpr hω
  have hK : 0<K := by dsimp only [K];positivity
  have hAω : A*ω=1 := inv_mul_cancel₀ hω.ne'
  have hraw := hu.affine_domain_actual a hR
  have hnorm := continuous_source_pair_affine_positive hraw hA m
  let v : Space n → ℝ := fun x => A*(u (T x)-m)
  let b : Space n → Space n := A • (fun x => R • g (T x))
  change WeakPSourcePair p (A^(p-1)*(R^p*c)) Ω' v b at hnorm
  have hDunit : LocalDomain (ball (0 : Space n) K) Ω' := by
    refine ⟨isOpen_ball,isBounded_ball,?_⟩
    intro x hx
    have hx0 : ‖x‖≤K := by
      simpa only [mem_closedBall,dist_zero_right] using closure_ball_subset_closedBall hx
    have hdist : dist (T x) a≤R*K := by
      simp only [T,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
      exact mul_le_mul_of_nonneg_left hx0 hR.le
    have hxB : T x∈closure (ball a (R*K)) := by
      rw [closure_ball _ (mul_pos hR hK).ne']
      exact mem_closedBall.mpr hdist
    exact hD.2.2 hxB
  have hrawbounds : ∀ᵐ x ∂volume.restrict (ball (0 : Space n) K),m≤u (T x)∧u (T x)≤M :=
    (continuous_ae_affine_ball_iff a hR K (fun y => m≤u y∧u y≤M)).mpr hbound
  have hvbounds : ∀ᵐ x ∂volume.restrict (ball (0 : Space n) K),0≤v x∧v x≤1 := by
    filter_upwards [hrawbounds] with x hx
    constructor
    · exact mul_nonneg hA.le (sub_nonneg.mpr hx.1)
    · exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 m) hA.le).trans_eq hAω
  have hsource' : |A^(p-1)*(R^p*c)|≤ε₀ := by
    calc
      |A^(p-1)*(R^p*c)|=A^(p-1)*(R^p*|c|) := by
        rw [abs_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg hA.le _),
          abs_of_nonneg (Real.rpow_nonneg hR.le _)]
      _≤A^(p-1)*(ε₀*ω^(p-1)) :=
        mul_le_mul_of_nonneg_left hsource (Real.rpow_nonneg hA.le _)
      _=ε₀ := by
        calc
          A^(p-1)*(ε₀*ω^(p-1))=ε₀*(A^(p-1)*ω^(p-1)) := by ring
          _=ε₀*(A*ω)^(p-1) := by rw [Real.mul_rpow hA.le hω.le]
          _=ε₀ := by rw [hAω,Real.one_rpow,mul_one]
  have hout := hunit hnorm hDunit hvbounds hsource'
  rcases hout with hup|hlo
  · left
    have hrawup : ∀ᵐ x ∂volume.restrict (ball (0 : Space n) (1/4 : ℝ)),u (T x)≤M-δ*ω := by
      filter_upwards [hup] with x hx
      have hh := mul_le_mul_of_nonneg_left hx hω.le
      change ω*(A*(u (T x)-m))≤ω*(1-δ) at hh
      have hcancel : ω*(A*(u (T x)-m))=u (T x)-m := by
        dsimp only [A]
        rw [←mul_assoc,mul_inv_cancel₀ hω.ne',one_mul]
      rw [hcancel] at hh
      have he : m+ω*(1-δ)=M-δ*ω := by dsimp only [ω];ring
      exact (by linarith only [hh] : u (T x)≤m+ω*(1-δ)).trans_eq he
    have ht := (continuous_ae_affine_ball_iff a hR (1/4)
      (fun y => u y≤M-δ*ω)).mp hrawup
    simpa only [div_eq_mul_inv,one_mul,ω] using ht
  · right
    have hrawlo : ∀ᵐ x ∂volume.restrict (ball (0 : Space n) (1/4 : ℝ)),m+δ*ω≤u (T x) := by
      filter_upwards [hlo] with x hx
      have hh := mul_le_mul_of_nonneg_left hx hω.le
      change ω*δ≤ω*(A*(u (T x)-m)) at hh
      have hcancel : ω*(A*(u (T x)-m))=u (T x)-m := by
        dsimp only [A]
        rw [←mul_assoc,mul_inv_cancel₀ hω.ne',one_mul]
      rw [hcancel] at hh
      linarith only [hh]
    have ht := (continuous_ae_affine_ball_iff a hR (1/4)
      (fun y => m+δ*ω≤u y)).mp hrawlo
    simpa only [div_eq_mul_inv,one_mul,ω] using ht

end BMCompactPDE
#print axioms BMCompactPDE.continuous_ae_affine_ball_iff
#print axioms BMCompactPDE.exists_source_spatial_oscillation_alternative
