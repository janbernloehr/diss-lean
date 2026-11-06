import NLS.KdV.HillComplexActionRatioNearFree

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillComplexActionGapPrefactor (k : ℕ) (p : Coeff 2) : ℂ :=
  sqrt (2*hillComplexActionGapRatio h0q h0r k p)

theorem exists_hillComplexActionGapPrefactor_common_analytic_bound :
    ∃ C : ℝ, 0<C ∧ ∀ B : ℝ, ∃ N : ℕ, 1≤N ∧ ∀ k : ℕ, N≤k →
      AnalyticOnNhd ℂ (hillComplexActionGapPrefactor h0q h0r k) (ball (0 : Coeff 2) B) ∧
      ∀ p∈ball (0 : Coeff 2) B,
        hillComplexActionGapPrefactor h0q h0r k p^2=2*hillComplexActionGapRatio h0q h0r k p ∧
        ‖hillComplexActionGapPrefactor h0q h0r k p‖^2≤C/(k:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := exists_hillComplexActionGapRatio_uniform_inverse_index_bound h0q h0r
  refine ⟨2*C,by positivity,?_⟩
  intro B
  obtain ⟨Nr,hNr,hr⟩ := exists_hillComplexActionGapRatio_uniform_near_free h0q h0r B (1/4) (by norm_num)
  obtain ⟨Na,hNa,ha⟩ := exists_hillComplexActionGapRatio_common_analytic h0q h0r B
  obtain ⟨Nb,hNb,hb⟩ := hbound B
  refine ⟨Nr+Na+Nb,hNr.trans (by omega),?_⟩
  intro k hk
  have hkr : Nr≤k := by omega
  have hka : Na≤k := by omega
  have hkb : Nb≤k := by omega
  have hk1 := hNr.trans hkr
  have hkpos : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hpB (p : Coeff 2) (hp : p∈ball (0 : Coeff 2) B) : ‖p‖≤B :=
    (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using hp).le
  refine ⟨?_,?_⟩
  · intro p hp
    have hn := hr p (hpB p hp) k hkr
    have hRe : 0<((2*(k:ℂ)*Real.pi)*hillComplexActionGapRatio h0q h0r k p).re := by
      have hh := (abs_re_le_norm ((2*(k:ℂ)*Real.pi)*hillComplexActionGapRatio h0q h0r k p-1)).trans hn
      simp only [sub_re,one_re] at hh
      have hl := (abs_le.mp hh).1
      linarith
    have hc : (2*(k:ℂ)*Real.pi)=((2*(k:ℝ)*Real.pi:ℝ):ℂ) := by simp only [ofReal_mul,ofReal_ofNat,ofReal_natCast]
    have hratio : 0<(hillComplexActionGapRatio h0q h0r k p).re := by
      apply (mul_pos_iff_of_pos_left (by positivity : 0<2*(k:ℝ)*Real.pi)).mp
      simpa only [hc,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] using hRe
    have hslit : 2*hillComplexActionGapRatio h0q h0r k p∈slitPlane := by
      rw [mem_slitPlane_iff]
      left
      simpa only [mul_re,re_ofNat,im_ofNat,zero_mul,sub_zero] using mul_pos (by norm_num : (0:ℝ)<2) hratio
    exact (Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds hslit)).comp
      (f := fun a : Coeff 2 => 2*hillComplexActionGapRatio h0q h0r k a)
      (analyticAt_const.mul (ha k hka p hp))
  · intro p hp
    refine ⟨complex_sqrt_sq _,?_⟩
    change ‖sqrt (2*hillComplexActionGapRatio h0q h0r k p)‖^2≤_
    rw [← norm_pow,complex_sqrt_sq,norm_mul,norm_ofNat]
    exact (mul_le_mul_of_nonneg_left (hb p (hpB p hp) k hkb) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring)

end NLS.KdV
