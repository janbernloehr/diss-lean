import NLS.KdV.HillFilledFreeGapAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFilledFreeGapUnit_bounded_complex_factorization (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : Coeff 2, ‖p‖ ≤ B → ∀ k : ℕ, N ≤ k → ∀ E : ℂ,
      hillL2Radicand p E=hillLocalGapPolynomial 0 h0q h0r k p E*hillFilledFreeGapUnit h0q h0r k (E,p) := by
  obtain ⟨N,hN,hpairs⟩ := exists_hillFreeGap_bounded_complex_localized_pairs h0q h0r 1 (by norm_num) le_rfl B
  refine ⟨N,hN,?_⟩
  intro p hp k hk E
  have hk1 : 1 ≤ k := hN.trans hk
  obtain ⟨hboundary,a,ha,b,hb,haz,hbz,hm⟩ := hpairs p hp k hk
  simp only [one_mul] at ha hb
  have hab (he : a=b) : deriv (hillL2Radicand p) a=0 := by
    apply deriv_eq_zero_of_two_zero_order (analyticOnNhd_hillL2Radicand p a (mem_univ _)) haz
    simpa [he] using hm a (ball_subset_closedBall ha)
  rw [hillLocalGapPolynomial_eq_of_pair 0 h0q h0r k hk1 p hboundary ha hb hm,
    hillFilledFreeGapUnit_eq_twoZeroQuotient h0q h0r k hk1 p hboundary ha hb haz hbz hm E]
  exact twoZeroQuotient_factor _ a b haz hbz hab E

end NLS.KdV
