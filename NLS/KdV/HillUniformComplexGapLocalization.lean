import NLS.KdV.HillLocalizedComplexGapPairs
import NLS.KdV.HillUniformComplexGapData

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_bounded_complex_midpoint_halfgap_localization
    (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ≤1) (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ p : Coeff 2, ‖p‖≤B → ∀ k : ℕ, N≤k →
      ‖hillLocalGapMidpoint 0 h0q h0r k p-(hillRealGapCenter 0 h0q h0r k : ℂ)‖ ≤
        ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ∧
      ‖sqrt (hillLocalGapSquare 0 h0q h0r k p/4)‖ ≤
        ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) := by
  obtain ⟨N,hN,hpairs⟩ := exists_hillFreeGap_bounded_complex_localized_pairs h0q h0r ρ hρ hρ1 B
  refine ⟨N,hN,?_⟩
  intro p hp k hk
  have hk1 := hN.trans hk
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  obtain ⟨hb,a,ha,b,hb',haz,hbz,horders⟩ := hpairs p hp k hk
  have haB : a∈ball c R := ball_subset_ball (mul_le_of_le_one_left hR.le hρ1) ha
  have hbB : b∈ball c R := ball_subset_ball (mul_le_of_le_one_left hR.le hρ1) hb'
  obtain ⟨hM,hS⟩ := hillLocalGapSymmetricData_eq_of_pair 0 h0q h0r k hk1 p hb haB hbB horders
  have had : ‖a-c‖≤ρ*R := (show ‖a-c‖<ρ*R by simpa only [mem_ball,dist_eq_norm] using ha).le
  have hbd : ‖b-c‖≤ρ*R := (show ‖b-c‖<ρ*R by simpa only [mem_ball,dist_eq_norm] using hb').le
  constructor
  · rw [hM,show (a+b)/2-c=((a-c)+(b-c))/2 by ring,norm_div]
    norm_num only [norm_ofNat]
    have hh := norm_add_le (a-c) (b-c)
    linarith
  · have hsquare : sqrt (hillLocalGapSquare 0 h0q h0r k p/4)^2=((b-a)/2)^2 := by
      rw [complex_sqrt_sq,hS]
      ring
    have he : ‖sqrt (hillLocalGapSquare 0 h0q h0r k p/4)‖=‖(b-a)/2‖ := by
      rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsquare with h | h
      · rw [h]
      · rw [h,norm_neg]
    rw [he,norm_div]
    norm_num only [norm_ofNat]
    have hh := norm_sub_le_norm_sub_add_norm_sub b c a
    rw [norm_sub_rev c a] at hh
    linarith

end NLS.KdV
