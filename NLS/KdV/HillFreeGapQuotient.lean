import NLS.KdV.HillLocalGapUnit
import NLS.KdV.HillScaledFreeZeroCounts

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGap_two_zero_data (k : ℕ) (hk : 1 ≤ k) :
    let c : ℂ := hillRealGapCenter 0 h0q h0r k
    let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
    hillL2Radicand 0 c=0 ∧ deriv (hillL2Radicand 0) c=0 ∧
      (∀ E ∈ sphere c R, hillL2Radicand 0 E≠0) ∧
      ∀ E ∈ closedBall c R, analyticOrderNatAt (hillL2Radicand 0) E=({c,c} : Multiset ℂ).count E := by
  dsimp only
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  have hzero : hillL2Radicand 0 c=0 := by
    dsimp only [c]
    rw [hillL2Radicand_zero,hillFreeGapCenter h0q h0r k hk,hillFreeGap_sqrt,Complex.sin_nat_mul_pi]
    norm_num
  have horder : analyticOrderNatAt (hillL2Radicand 0) c=2 := by
    dsimp only [c]
    rw [hillFreeGapCenter h0q h0r k hk]
    exact hillL2Radicand_free_order k hk
  have hder := deriv_eq_zero_of_two_zero_order (analyticOnNhd_hillL2Radicand 0 c (mem_univ _)) hzero horder
  have hboundary (E : ℂ) (hE : E ∈ sphere c R) : hillL2Radicand 0 E≠0 := by
    intro hz
    have he := hillScaledFreeGapContour_zero_unique h0q h0r 1 le_rfl k hk E
      (by simpa only [one_mul] using sphere_subset_closedBall hE) hz
    have hh : dist E c=R := hE
    rw [he,dist_self] at hh
    linarith
  refine ⟨hzero,hder,hboundary,?_⟩
  intro E hE
  have hfilled := hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r k hk hE
  have ho := analyticOrderNatAt_hillL2Radicand_in_filled_gap 0 h0q h0r k hk E hfilled
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r k hk
  simpa only [map_zero,hl,hu,hillFreeGapCenter h0q h0r k hk] using ho

theorem hillFreeGap_twoZeroQuotient_unit (k : ℕ) (hk : 1 ≤ k) :
    let c : ℂ := hillRealGapCenter 0 h0q h0r k
    let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
    AnalyticOnNhd ℂ (twoZeroQuotient (hillL2Radicand 0) c c) (closedBall c R) ∧
      (∀ E ∈ closedBall c R, twoZeroQuotient (hillL2Radicand 0) c c E≠0) ∧
      ∀ E ∈ ball c R, hillLocalGapUnit 0 h0q h0r k (E,0)=twoZeroQuotient (hillL2Radicand 0) c c E := by
  dsimp only
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  have hcB : c ∈ ball c R := mem_ball_self hR
  have hcK := ball_subset_closedBall hcB
  have ha := (analyticOnNhd_hillL2Radicand 0).mono (subset_univ (closedBall c R))
  obtain ⟨hz,hd,hb,hm⟩ := hillFreeGap_two_zero_data h0q h0r k hk
  refine ⟨analyticOnNhd_twoZeroQuotient _ _ c c ha hcK hcK,?_,?_⟩
  · intro E hE
    apply twoZeroQuotient_ne_zero _ _ c c E ha hcK hcK hE hz hz (fun _ => hd)
    · intro hzero
      exact Or.inl (hillScaledFreeGapContour_zero_unique h0q h0r 1 le_rfl k hk E (by simpa only [one_mul] using hE) hzero)
    · exact fun _ => hm E hE
  · intro E hE
    exact hillLocalGapUnit_eq_twoZeroQuotient 0 h0q h0r k hk 0 hb hcB hcB hz hz hm hE

end NLS.KdV
