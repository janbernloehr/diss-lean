import NLS.KdV.HillUniformComplexGapData
import NLS.KdV.HillLocalizedComplexGapPairs

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_bounded_real_midpoint_halfgap_localization
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖ ≤ B →
        ∀ k : ℕ, N ≤ k →
          ‖(hillRealGapCenter q hq hr k : ℂ)-(hillRealGapCenter 0 h0q h0r k : ℂ)‖ ≤
            ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ∧
          ‖(hillRealGapHalfLength q hq hr k : ℂ)‖ ≤
            ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) := by
  obtain ⟨Np,hNp,hpairs⟩ := exists_hillFreeGap_bounded_complex_localized_pairs h0q h0r ρ hρ hρ1 B
  obtain ⟨Ns,hNs,hphysical⟩ := exists_hillFreeGap_bounded_real_symmetric_data_matching h0q h0r B
  refine ⟨max Np Ns,hNp.trans (le_max_left _ _),?_⟩
  intro q hq hr hp k hk
  have hkp : Np ≤ k := (le_max_left _ _).trans hk
  have hks : Ns ≤ k := (le_max_right _ _).trans hk
  have hk1 : 1 ≤ k := hNp.trans hkp
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  obtain ⟨hboundary,a,ha,b,hb,haz,hbz,hm⟩ := hpairs (SpectralWeight.one.toCoeff q) hp k hkp
  have haB : a ∈ ball c R := ball_subset_ball (mul_le_of_le_one_left hR.le hρ1) ha
  have hbB : b ∈ ball c R := ball_subset_ball (mul_le_of_le_one_left hR.le hρ1) hb
  obtain ⟨hM,hS⟩ := hillLocalGapSymmetricData_eq_of_pair 0 h0q h0r k hk1 _ hboundary haB hbB hm
  obtain ⟨hMp,hSp⟩ := hphysical q hq hr hp k hks
  have hτ : (hillRealGapCenter q hq hr k : ℂ)=(a+b)/2 := hMp.symm.trans hM
  have hδ : (2*(hillRealGapHalfLength q hq hr k : ℂ))^2=(b-a)^2 := hSp.symm.trans hS
  have had : ‖a-c‖ ≤ ρ*R := (show ‖a-c‖ < ρ*R by simpa only [mem_ball,dist_eq_norm] using ha).le
  have hbd : ‖b-c‖ ≤ ρ*R := (show ‖b-c‖ < ρ*R by simpa only [mem_ball,dist_eq_norm] using hb).le
  constructor
  · rw [hτ,show (a+b)/2-c=((a-c)+(b-c))/2 by ring,norm_div,norm_ofNat]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hh := norm_add_le (a-c) (b-c)
    linarith
  · have hd : ‖b-a‖ ≤ 2*(ρ*R) := by
      have hh := norm_sub_le_norm_sub_add_norm_sub b c a
      rw [norm_sub_rev c a] at hh
      linarith
    have hh := congrArg norm hδ
    rw [norm_pow,norm_mul,norm_ofNat,norm_pow] at hh
    have hs := sq_le_sq₀ (norm_nonneg (b-a)) (by positivity : 0 ≤ 2*(ρ*R)) |>.mpr hd
    have hnorm : 2*‖(hillRealGapHalfLength q hq hr k : ℂ)‖ ≤ 2*(ρ*R) :=
      (sq_le_sq₀ (by positivity) (by positivity)).mp (hh.trans_le hs)
    change ‖(hillRealGapHalfLength q hq hr k : ℂ)‖ ≤ ρ*R
    linarith

end NLS.KdV
