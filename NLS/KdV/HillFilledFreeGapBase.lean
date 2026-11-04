import NLS.KdV.HillFilledFreeGapUnit
import NLS.KdV.HillFreeGapQuotient
import NLS.KdV.HillLocalDeflatedComplexRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFilledFreeGapUnit_zero_eq_quotient (k : ℕ) (hk : 1 ≤ k) (E : ℂ) :
    hillFilledFreeGapUnit h0q h0r k (E,0)=twoZeroQuotient (hillL2Radicand 0)
      (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapCenter 0 h0q h0r k : ℂ) E := by
  have hR := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  obtain ⟨hz,_,hb,hm⟩ := hillFreeGap_two_zero_data h0q h0r k hk
  exact hillFilledFreeGapUnit_eq_twoZeroQuotient h0q h0r k hk 0 hb (mem_ball_self hR) (mem_ball_self hR) hz hz hm E

theorem hillFilledFreeGapUnit_zero_eq_physical_sq (k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) :
    hillFilledFreeGapUnit h0q h0r k (E,0)=hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E^2 := by
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  by_cases hB : E ∈ ball c R
  · rw [hillFilledFreeGapUnit_eq_local h0q h0r k 0 E hB]
    simpa only [map_zero] using hillLocalGapUnit_at_base 0 h0q h0r k hk E hB
  · have hR := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
      (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
    have hEc : E-c≠0 := sub_ne_zero.mpr (fun he => hB (he ▸ mem_ball_self hR))
    have hf := hillL2Radicand_eq_gap_polynomial_mul_deflated_sq 0 h0q h0r k hk E
      (hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r k hk hE)
    obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r k hk
    have hcenter := hillFreeGapCenter h0q h0r k hk
    rw [map_zero,hl,hu,← hcenter] at hf
    obtain ⟨hz,_,hb,hm⟩ := hillFreeGap_two_zero_data h0q h0r k hk
    have hP := hillLocalGapPolynomial_eq_of_pair 0 h0q h0r k hk 0 hb (mem_ball_self hR) (mem_ball_self hR) hm E
    rw [hillFilledFreeGapUnit,if_neg hB,hP,hf]
    exact mul_div_cancel_left₀ _ (mul_ne_zero hEc hEc)

theorem hillFilledFreeGapUnit_zero_ne_zero (k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) :
    hillFilledFreeGapUnit h0q h0r k (E,0)≠0 := by
  rw [hillFilledFreeGapUnit_zero_eq_quotient h0q h0r k hk E]
  exact (hillFreeGap_twoZeroQuotient_unit h0q h0r k hk).2.1 E hE

end NLS.KdV
