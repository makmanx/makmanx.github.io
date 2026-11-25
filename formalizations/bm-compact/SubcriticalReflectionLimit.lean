import SubcriticalSphereTrapping
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory InnerProductSpace Metric Bornology
open scoped Topology ENNReal ContDiff
namespace BMCompactPDE

/-- Fixed additive radial separation from reflection order forces the two
radial envelopes of a decaying exterior solution to have one common limit. -/
theorem WeakPHarmonicPair.subcritical_normalized_limit_of_separated_order
    {n : ℕ} {p R D : ℝ} (hn : 2≤n) (hpn : p<(n:ℝ)) (hR : 0<R) (hD : 0<D)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p (closedBall (0:Space n) R)ᶜ u g)
    (hc : ContinuousOn u (ball (0:Space n) R)ᶜ) (hl : Tendsto u (cocompact _) (𝓝 0))
    (horder : ∀ x y, R≤‖x‖ → ‖x‖+D≤‖y‖ → u y≤u x) :
    ∃ c : ℝ, Tendsto (fun x => ‖x‖^(((n:ℝ)-p)/(p-1))*u x) (cocompact _) (𝓝 c) := by
  classical
  have : NeZero n := ⟨by omega⟩
  let α := ((n:ℝ)-p)/(p-1)
  let r := fun j : ℕ => R+(j:ℝ)*D
  have hmono : Monotone r := fun j k hjk => add_le_add_right (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr hjk) hD.le) R
  have hge (j : ℕ) : R ≤ r j := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hD.le)
  have hr (j : ℕ) := hR.trans_le (hge j)
  have hrnext (j : ℕ) : r (j+1) = r j+D := by dsimp only [r]; push_cast; ring
  let S := fun j => sphere (0:Space n) (r j)
  have hnorm (j : ℕ) {x : Space n} (hx : x∈S j) : ‖x‖=r j := by
    simpa only [S,mem_sphere,dist_zero_right] using hx
  have hsC (j : ℕ) : ContinuousOn u (S j) := hc.mono (fun x hx => by
    simpa only [mem_compl_iff,mem_ball,dist_zero_right,not_lt,hnorm j hx] using hge j)
  have hsne (j : ℕ) : (S j).Nonempty := NormedSpace.sphere_nonempty.mpr (hr j).le
  choose X hx hxMin using (fun j => (isCompact_sphere (0:Space n) (r j)).exists_isMinOn (hsne j) (hsC j))
  choose Y hy hyMax using (fun j => (isCompact_sphere (0:Space n) (r j)).exists_isMaxOn (hsne j) (hsC j))
  let m := fun j => (r j)^α*u (X j)
  let M := fun j => (r j)^α*u (Y j)
  have htr (j : ℕ) : ∀ x, r j≤‖x‖ → m j≤‖x‖^α*u x ∧ ‖x‖^α*u x≤M j := by
    have hsub : (closedBall (0:Space n) (r j))ᶜ ⊆ (closedBall 0 R)ᶜ :=
      compl_subset_compl.mpr (closedBall_subset_closedBall (hge j))
    have hcsub : (ball (0:Space n) (r j))ᶜ ⊆ (ball 0 R)ᶜ :=
      compl_subset_compl.mpr (ball_subset_ball (hge j))
    apply (hu.mono hsub isClosed_closedBall.isOpen_compl).subcritical_normalized_trapping_on_sphere
      hn hpn (hr j) (hc.mono hcsub) hl
    intro z hz
    exact ⟨mul_le_mul_of_nonneg_left (hxMin j hz) (Real.rpow_nonneg (hr j).le _),
      mul_le_mul_of_nonneg_left (hyMax j hz) (Real.rpow_nonneg (hr j).le _)⟩
  have hm : Monotone m := by
    intro j k hjk
    have he := hnorm k (hx k)
    exact (htr j (X k) ((hmono hjk).trans_eq he.symm)).1.trans_eq (by rw [he])
  have hb : BddAbove (range m) := by
    refine ⟨M 0,?_⟩
    rintro _ ⟨j,rfl⟩
    have he := hnorm j (hx j)
    simpa only [he,m] using (htr 0 (X j) ((hmono (Nat.zero_le j)).trans_eq he.symm)).2
  let c := ⨆ j, m j
  have hmL : Tendsto m atTop (𝓝 c) := tendsto_atTop_ciSup hm hb
  have hrtop : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_left atTop R (tendsto_natCast_atTop_atTop.atTop_mul_const hD)
  have hratio : Tendsto (fun j => r (j+1)/r j) atTop (𝓝 1) := by
    have ht := (tendsto_inv_atTop_zero.comp hrtop).const_mul D
    have ht' := (tendsto_const_nhds (x:=(1:ℝ))).add ht
    simp only [mul_zero,add_zero] at ht'
    apply ht'.congr
    intro j
    rw [hrnext,add_div,div_self (hr j).ne',div_eq_mul_inv]
    rfl
  have hratpow := (Real.continuousAt_rpow_const 1 α (Or.inl one_ne_zero)).tendsto.comp hratio
  let Q := fun j => (r (j+1)/r j)^α*m j
  have hQL : Tendsto Q atTop (𝓝 c) := by simpa only [Function.comp_def,Real.one_rpow,one_mul] using hratpow.mul hmL
  have hupper (j : ℕ) : M (j+1)≤Q j := by
    have heX := hnorm j (hx j)
    have heY := hnorm (j+1) (hy (j+1))
    have ho := horder (X j) (Y (j+1)) ((hge j).trans_eq heX.symm) (by rw [heX,heY,hrnext])
    have hpow := Real.rpow_pos_of_pos (hr j) α
    calc
      _ ≤ (r (j+1))^α * u (X j) := mul_le_mul_of_nonneg_left ho (Real.rpow_nonneg (hr _).le _)
      _ = _ := by dsimp only [Q,m];rw [Real.div_rpow (hr _).le (hr _).le];field_simp [hpow.ne']
  refine ⟨c,Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  obtain ⟨j,hmj,hQj⟩ := ((Metric.tendsto_nhds.mp hmL ε hε).and (Metric.tendsto_nhds.mp hQL ε hε)).exists
  filter_upwards [tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop (r (j+1)))] with x hxj
  have hlo := (htr j x ((hmono (Nat.le_succ j)).trans hxj)).1
  have hhi := (htr (j+1) x hxj).2.trans (hupper j)
  rw [Real.dist_eq,abs_lt] at hmj hQj ⊢
  change -ε < ‖x‖^α*u x-c ∧ ‖x‖^α*u x-c<ε
  constructor <;> linarith only [hmj.1,hQj.2,hlo,hhi]

/-- Positivity of the scalar on the enclosing sphere makes the common
normalized limit strictly positive. -/
theorem WeakPHarmonicPair.subcritical_positive_normalized_limit_of_separated_order
    {n : ℕ} {p R D : ℝ} (hn : 2≤n) (hpn : p<(n:ℝ)) (hR : 0<R) (hD : 0<D)
    {u : Space n → ℝ} {g : Space n → Space n}
    (hu : WeakPHarmonicPair p (closedBall (0:Space n) R)ᶜ u g)
    (hc : ContinuousOn u (ball (0:Space n) R)ᶜ) (hl : Tendsto u (cocompact _) (𝓝 0))
    (horder : ∀ x y, R≤‖x‖ → ‖x‖+D≤‖y‖ → u y≤u x)
    (hpos : ∀ x∈sphere (0:Space n) R, 0<u x) :
    ∃ c : ℝ, 0<c ∧ Tendsto (fun x => ‖x‖^(((n:ℝ)-p)/(p-1))*u x) (cocompact _) (𝓝 c) := by
  have : NeZero n := ⟨by omega⟩
  let α := ((n:ℝ)-p)/(p-1)
  obtain ⟨c,hcL⟩ := hu.subcritical_normalized_limit_of_separated_order hn hpn hR hD hc hl horder
  have hsc : ContinuousOn u (sphere (0:Space n) R) := hc.mono (fun x hx =>
    not_lt.mpr (mem_sphere.mp hx).ge)
  have hne : (sphere (0:Space n) R).Nonempty := NormedSpace.sphere_nonempty.mpr hR.le
  obtain ⟨x,hx,hmin⟩ := (isCompact_sphere (0:Space n) R).exists_isMinOn hne hsc
  obtain ⟨y,_,hmax⟩ := (isCompact_sphere (0:Space n) R).exists_isMaxOn hne hsc
  have hpw := Real.rpow_pos_of_pos hR α
  have htr := hu.subcritical_normalized_trapping_on_sphere hn hpn hR hc hl
    (a:=R^α*u x) (b:=R^α*u y) (fun z hz => ⟨mul_le_mul_of_nonneg_left (hmin hz) hpw.le,
      mul_le_mul_of_nonneg_left (hmax hz) hpw.le⟩)
  have hev : ∀ᶠ z : Space n in cocompact _, R≤‖z‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop R)
  exact ⟨c,(mul_pos hpw (hpos x hx)).trans_le (ge_of_tendsto hcL (hev.mono (fun z hz => (htr z hz).1))),hcL⟩

/-- Exterior-continuous representatives preserve radial separation order
beyond a slightly larger radius and gap. Both variables can be approximated
independently by points where the raw and selected scalars agree. -/
theorem exterior_separated_order_of_ae_eq {n : ℕ} {R D : ℝ} (hD : 0≤D)
    {u v : Space n → ℝ} (heq : u =ᵐ[volume] v)
    (hc : ContinuousOn u (closedBall (0:Space n) R)ᶜ)
    (ho : ∀ x y, R≤‖x‖ → ‖x‖+D≤‖y‖ → v y≤v x) :
    ∀ x y, R+1≤‖x‖ → ‖x‖+(D+1)≤‖y‖ → u y≤u x := by
  intro x y hx hxy
  by_contra! hbad
  let t := (u x+u y)/2
  have hxt : u x<t := by dsimp only [t]; linarith
  have hyt : t<u y := by dsimp only [t]; linarith
  have hRx : R<‖x‖ := by linarith
  have hRy : R<‖y‖ := by linarith
  have hxc := hc.continuousAt (isClosed_closedBall.isOpen_compl.mem_nhds
    (by simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hRx))
  have hyc := hc.continuousAt (isClosed_closedBall.isOpen_compl.mem_nhds
    (by simpa only [mem_compl_iff,mem_closedBall,dist_zero_right,not_le] using hRy))
  have hd : Dense {z | u z=v z} := (volume : Measure (Space n)).dense_of_ae heq
  have hrx : ∀ᶠ z in 𝓝 x, R<‖z‖ := continuous_norm.continuousAt.tendsto.eventually (eventually_gt_nhds hRx)
  have hnx : ∀ᶠ z in 𝓝 x, ‖z‖<‖x‖+1/4 := continuous_norm.continuousAt.tendsto.eventually
    (eventually_lt_nhds (by linarith : ‖x‖<‖x‖+1/4))
  have hny : ∀ᶠ z in 𝓝 y, ‖y‖-1/4<‖z‖ := continuous_norm.continuousAt.tendsto.eventually
    (eventually_gt_nhds (by linarith : ‖y‖-1/4<‖y‖))
  obtain ⟨x',⟨⟨hR',hn'⟩,hux⟩,hx'⟩ := mem_closure_iff_nhds.mp (hd x) _
    ((hrx.and hnx).and (hxc.tendsto.eventually (eventually_lt_nhds hxt)))
  obtain ⟨y',⟨hn'',huy⟩,hy'⟩ := mem_closure_iff_nhds.mp (hd y) _
    (hny.and (hyc.tendsto.eventually (eventually_gt_nhds hyt)))
  have heX : u x'=v x' := hx'
  have heY : u y'=v y' := hy'
  have hgap : ‖x'‖+D≤‖y'‖ := by linarith only [hn',hn'',hxy]
  have hh := ho x' y' hR'.le hgap
  rw [←heX,←heY] at hh
  exact (not_lt.mpr hh) (hux.trans huy)

end BMCompactPDE
#print axioms BMCompactPDE.WeakPHarmonicPair.subcritical_normalized_limit_of_separated_order

#print axioms BMCompactPDE.exterior_separated_order_of_ae_eq

#print axioms BMCompactPDE.WeakPHarmonicPair.subcritical_positive_normalized_limit_of_separated_order
