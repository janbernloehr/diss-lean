import NLS.KdV.HillUniformComplexActionRatioBounds
import NLS.KdV.HillCommonActionGapRatioPhysical
import NLS.KdV.HillFreeActionGapRatio
import Mathlib.Analysis.Complex.Schwarz

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillComplexActionGapRatio_uniform_near_free (B ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, 1≤N ∧ ∀ p : Coeff 2, ‖p‖≤B → ∀ k : ℕ, N≤k →
      ‖(2*(k:ℂ)*Real.pi)*hillComplexActionGapRatio h0q h0r k p-1‖≤ε := by
  obtain ⟨C,hC,hbound⟩ := exists_hillComplexActionGapRatio_uniform_inverse_index_bound h0q h0r
  let M := 2*Real.pi*C+1
  let B0 := max 1 B
  let T := B0+M*B0/ε+1
  have hM : 0<M := by dsimp only [M];positivity
  have hB0 : 0<B0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBT : B<T := by
    have hh : B≤B0 := le_max_right _ _
    dsimp only [T]
    have hd : 0<M*B0/ε := by positivity
    linarith
  have hT : 0<T := by dsimp only [T];positivity
  have hscale : M*B0≤ε*T := by
    have hd : ε*(M*B0/ε)=M*B0 := by field_simp
    dsimp only [T]
    nlinarith [mul_pos hε hB0]
  obtain ⟨Nb,hNb,hb⟩ := hbound T
  obtain ⟨Na,hNa,ha⟩ := exists_hillComplexActionGapRatio_common_analytic h0q h0r T
  obtain ⟨Nf,hNf,hf⟩ := exists_hillComplexActionGapRatio_bounded_real_physical_matching h0q h0r 0
  refine ⟨Nb+Na+Nf,hNb.trans (by omega),?_⟩
  intro p hp k hk
  have hkb : Nb≤k := by omega
  have hka : Na≤k := by omega
  have hkf : Nf≤k := by omega
  have hk1 := hNb.trans hkb
  have hkpos : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hkn : (2*(k:ℂ)*Real.pi)≠0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast (show k≠0 by omega))) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  let F : Coeff 2 → ℂ := fun a => (2*(k:ℂ)*Real.pi)*hillComplexActionGapRatio h0q h0r k a
  have hF : AnalyticOnNhd ℂ F (ball (0 : Coeff 2) T) := analyticOnNhd_const.mul (ha k hka)
  have hF0 : F 0=1 := by
    have hh := (hf 0 h0q h0r (by simp) k hkf).trans (hillActionGapRatio_zero h0q h0r k hk1)
    rw [map_zero] at hh
    change (2*(k:ℂ)*Real.pi)*hillComplexActionGapRatio h0q h0r k 0=1
    rw [hh,mul_inv_cancel₀ hkn]
  have hnorm (a : Coeff 2) (ha : a∈ball (0 : Coeff 2) T) : ‖F a‖≤2*Real.pi*C := by
    have haT : ‖a‖≤T := (show ‖a‖<T by simpa only [mem_ball,dist_zero_right] using ha).le
    change ‖(2*(k:ℂ)*Real.pi)*hillComplexActionGapRatio h0q h0r k a‖≤_
    rw [norm_mul,norm_mul,norm_mul,norm_ofNat,Complex.norm_natCast,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left (hb a haT k hkb) (by positivity : 0≤2*(k:ℝ)*Real.pi)).trans_eq (by field_simp)
  have hmaps : MapsTo F (ball (0 : Coeff 2) T) (closedBall (F 0) M) := by
    intro a ha
    rw [mem_closedBall,hF0,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by rw [norm_one];dsimp only [M];linarith [hnorm a ha])
  have hpT : p∈ball (0 : Coeff 2) T := by rw [mem_ball,dist_zero_right];exact hp.trans_lt hBT
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball hF.differentiableOn hmaps hpT
  rw [hF0,dist_eq_norm,dist_zero_right] at hschwarz
  change ‖F p-1‖≤ε
  apply hschwarz.trans
  have hpn : ‖p‖≤B0 := hp.trans (le_max_right _ _)
  have hh := mul_le_mul_of_nonneg_left hpn (by positivity : 0≤M/T)
  apply hh.trans
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hT).mpr hscale

end NLS.KdV
