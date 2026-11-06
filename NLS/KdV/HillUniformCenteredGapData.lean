import NLS.KdV.HillLocalizedComplexGapPairs
import NLS.KdV.HillUniformComplexGapData

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Original localized complex endpoints give common centered midpoint
and squared half-gap bounds, without choosing either endpoint analytically. -/
theorem exists_hillLocalGap_bounded_centered_data
    (ρ : ℝ) (hρ : 0<ρ) (hρ1 : ρ≤1) (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ k : ℕ, N≤k →
      AnalyticOnNhd ℂ (hillLocalGapMidpoint 0 h0q h0r k) (ball (0 : Coeff 2) B) ∧
      AnalyticOnNhd ℂ (fun p => hillLocalGapSquare 0 h0q h0r k p/4) (ball (0 : Coeff 2) B) ∧
      ∀ p : Coeff 2, ‖p‖≤B →
        ‖hillLocalGapMidpoint 0 h0q h0r k p-(hillRealGapCenter 0 h0q h0r k : ℂ)‖<
          ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ∧
        ‖hillLocalGapSquare 0 h0q h0r k p/4‖<
          (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k))^2 := by
  obtain ⟨Np,hNp,hpairs⟩ := exists_hillFreeGap_bounded_complex_localized_pairs h0q h0r ρ hρ hρ1 B
  obtain ⟨Ns,hNs,hsym⟩ := exists_hillFreeGap_bounded_complex_analytic_symmetric_data h0q h0r B
  refine ⟨max Np Ns,hNp.trans (le_max_left _ _),?_⟩
  intro k hk
  have hkP : Np≤k := (le_max_left _ _).trans hk
  have hkS : Ns≤k := (le_max_right _ _).trans hk
  have hk1 : 1≤k := hNp.trans hkP
  refine ⟨(hsym k hkS).1,(hsym k hkS).2.1.div_const,?_⟩
  intro p hp
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  obtain ⟨hboundary,a,ha,b,hb,_,_,horders⟩ := hpairs p hp k hkP
  have haB : a∈ball c R := ball_subset_ball (mul_le_of_le_one_left hR.le hρ1) ha
  have hbB : b∈ball c R := ball_subset_ball (mul_le_of_le_one_left hR.le hρ1) hb
  obtain ⟨hMid,hSq⟩ := hillLocalGapSymmetricData_eq_of_pair 0 h0q h0r k hk1 p hboundary haB hbB horders
  have ha' : ‖a-c‖<ρ*R := by simpa only [mem_ball,dist_eq_norm] using ha
  have hb' : ‖b-c‖<ρ*R := by simpa only [mem_ball,dist_eq_norm] using hb
  constructor
  · rw [hMid,show (a+b)/2-c=((a-c)+(b-c))/2 by ring,norm_div]
    norm_num only [norm_ofNat]
    apply (div_lt_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    exact (norm_add_le _ _).trans_lt (by linarith)
  · rw [hSq,norm_div,norm_pow]
    norm_num only [norm_ofNat]
    apply (div_lt_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have hd := norm_sub_le_norm_sub_add_norm_sub b c a
    rw [norm_sub_rev c a] at hd
    have hdiff : ‖b-a‖<2*(ρ*R) := by linarith
    nlinarith [mul_pos hρ hR,norm_nonneg (b-a)]

end NLS.KdV
