import BallGreenCapacityEquality
import CriticalOuterLaws
import GreenObstacleOrder
import SingletonGreen

noncomputable section
set_option autoImplicit false
open Set Filter Bornology
open scoped Topology Pointwise
namespace BMCompactPDE

private theorem translated_asymptotic {n : ℕ} {σ p k : ℝ} (hn : 1<(n:ℝ)) (hp : (n:ℝ)≤p)
    {G : Space n → ℝ} (hk : HasGreenAsymptotic n σ p G k) (a : Space n) :
    HasGreenAsymptotic n σ p (fun x=>G (x-a)) k := by
  have ht := (hk.comp (tendsto_sub_const_cobounded a)).add (tendsto_fundamentalPotential_translate_sub n σ hn hp a)
  rw [add_zero] at ht
  apply ht.congr
  intro x
  change (G (x-a)-fundamentalPotential n σ p (x-a)) +
    (fundamentalPotential n σ p (x-a)-fundamentalPotential n σ p x) = G (x-a)-fundamentalPotential n σ p x
  ring

theorem HasFiniteGreenCapacity.translate {n : ℕ} {σ p c : ℝ} {K : Set (Space n)}
    (hc : HasFiniteGreenCapacity σ p K c) (a : Space n) : HasFiniteGreenCapacity σ p (K+{a}) c := by
  obtain ⟨G,k,hG,hk,rfl⟩ := hc
  have h' := hG.translate_actual a
  have he : (fun x : Space n=>x+a) '' K = K+{a} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,hy,a,rfl,rfl⟩
    · rintro ⟨y,hy,z,hz,rfl⟩
      obtain rfl : z=a := hz
      exact ⟨y,hy,rfl⟩
  rw [he] at h'
  exact ⟨_,k,h',translated_asymptotic hG.1 hG.2.1 hk a,rfl⟩

theorem IsExteriorGreen.supercritical_constant_nonpos {n : ℕ} {σ p k : ℝ}
    (hnp : (n:ℝ)<p) {K : Set (Space n)} {G : Space n → ℝ}
    (hG : IsExteriorGreen n σ p K G) (hk : HasGreenAsymptotic n σ p G k) : k≤0 := by
  obtain ⟨a,ha⟩ := hG.2.2.2.2.1
  have h0 := (isExteriorGreen_singleton_fundamentalPotential n hG.2.2.1 hG.1 hnp).translate_actual a
  have hA := translated_asymptotic hG.1 hnp.le (hasGreenAsymptotic_fundamentalPotential n σ p) a
  apply h0.asymptotic_constant_antitone_obstacle hG _ hA hk
  rintro _ ⟨y,hy,rfl⟩
  obtain rfl : y=(0:Space n) := hy
  simpa using ha

theorem HasFiniteGreenCapacity.dilate_supercritical {n : ℕ} {σ p c ρ : ℝ} {K : Set (Space n)}
    (hc : HasFiniteGreenCapacity σ p K c) (hpn : (n:ℝ)<p) (hρ : 0<ρ) :
    HasFiniteGreenCapacity σ p (ρ • K) (ρ^(p-(n:ℝ))*c) := by
  obtain ⟨G,k,hG,hk,rfl⟩ := hc
  let β := (p-(n:ℝ))/(p-1)
  let m := ρ^β
  have hm : 0<m := Real.rpow_pos_of_pos hρ _
  have hk0 := hG.supercritical_constant_nonpos hpn hk
  have hp1 := sub_pos.mpr (hG.1.trans hpn)
  have hb : β*(p-1)=p-(n:ℝ) := div_mul_cancel₀ _ hp1.ne'
  have hpre : (fun x : Space n=>ρ⁻¹ • x) ⁻¹' Kᶜ=(ρ • K)ᶜ := by
    ext x;exact not_congr (mem_smul_set_iff_inv_smul_mem₀ hρ.ne' K x).symm
  have hi : Tendsto (fun x : Space n => ρ⁻¹ • x) (cobounded (Space n)) (cobounded (Space n)) := by
    apply tendsto_norm_atTop_iff_cobounded.mp
    simpa only [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hρ).le] using
      ((tendsto_norm_cobounded_atTop : Tendsto (fun x : Space n => ‖x‖) _ _).const_mul_atTop (inv_pos.mpr hρ))
  have hlim : HasGreenAsymptotic n σ p (fun x=>m*G (ρ⁻¹ • x)) (m*k) := by
    apply ((hk.comp hi).const_mul m).congr
    intro x
    change m*(G (ρ⁻¹ • x)- fundamentalPotential n σ p (ρ⁻¹ • x)) = m*G (ρ⁻¹ • x)-fundamentalPotential n σ p x
    rw [fundamentalPotential_dilate_supercritical n σ hpn (inv_pos.mpr hρ),Real.inv_rpow hρ.le]
    change m*(_-m⁻¹*_)=_
    rw [mul_sub,←mul_assoc,mul_inv_cancel₀ hm.ne',one_mul]
  obtain ⟨g,hg⟩ := hG.2.2.2.2.2.2.2.1
  have hd := hg.source_zero.dilation_actual (inv_pos.mpr hρ)
  rw [mul_zero,hpre] at hd
  have hnw : IsExteriorGreen n σ p (ρ • K) (fun x=>m*G (ρ⁻¹ • x)) := by
    refine ⟨hG.1,hpn.le,hG.2.2.1,hG.2.2.2.1.smul _,hG.2.2.2.2.1.smul_set,
      (hG.2.2.2.2.2.1.comp (continuous_const_smul _)).const_mul _,?_,⟨_,hd.harmonic_of_source_zero.smul m⟩,
      hlim.boundedRemainder⟩
    intro x hx
    change m*G (ρ⁻¹ • x)=0
    rw [hG.2.2.2.2.2.2.1 ((mem_smul_set_iff_inv_smul_mem₀ hρ.ne' K x).mp hx),mul_zero]
  refine ⟨_,_,hnw,hlim,?_⟩
  simp only [greenCapacityOfConstant,if_neg hpn.ne',←mul_neg,m,Real.mul_rpow hm.le (neg_nonneg.mpr hk0),
    ←Real.rpow_mul hρ.le,hb]

end BMCompactPDE
#print axioms BMCompactPDE.HasFiniteGreenCapacity.translate
#print axioms BMCompactPDE.IsExteriorGreen.supercritical_constant_nonpos
#print axioms BMCompactPDE.HasFiniteGreenCapacity.dilate_supercritical
