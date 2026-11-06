import NLS.KdV.HillUniformComplexGapUnit
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

def hillFilledFreeGapUnit (k : ℕ) (t : ℂ × Coeff 2) : ℂ :=
  if t.1 ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)
  then hillLocalGapUnit 0 h0q h0r k t
  else hillL2Radicand t.2 t.1/hillLocalGapPolynomial 0 h0q h0r k t.2 t.1

theorem hillFilledFreeGapUnit_eq_local (k : ℕ) (p : Coeff 2) (E : ℂ)
    (hE : E ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) :
    hillFilledFreeGapUnit h0q h0r k (E,p)=hillLocalGapUnit 0 h0q h0r k (E,p) := by
  exact if_pos hE

theorem hillFilledFreeGapUnit_eq_twoZeroQuotient (k : ℕ) (hk : 1 ≤ k) (p : Coeff 2)
    (hboundary : ∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k), hillL2Radicand p E≠0)
    {a b : ℂ}
    (ha : a ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k))
    (hb : b ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k))
    (haz : hillL2Radicand p a=0) (hbz : hillL2Radicand p b=0)
    (hm : ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      analyticOrderNatAt (hillL2Radicand p) E=({a,b} : Multiset ℂ).count E) (E : ℂ) :
    hillFilledFreeGapUnit h0q h0r k (E,p)=twoZeroQuotient (hillL2Radicand p) a b E := by
  by_cases hE : E ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)
  · rw [hillFilledFreeGapUnit_eq_local h0q h0r k p E hE]
    exact hillLocalGapUnit_eq_twoZeroQuotient 0 h0q h0r k hk p hboundary ha hb haz hbz hm hE
  · have haE : E-a≠0 := sub_ne_zero.mpr (fun he => hE (he ▸ ha))
    have hbE : E-b≠0 := sub_ne_zero.mpr (fun he => hE (he ▸ hb))
    have hab (he : a=b) : deriv (hillL2Radicand p) a=0 := by
      apply deriv_eq_zero_of_two_zero_order (analyticOnNhd_hillL2Radicand p a (mem_univ _)) haz
      simpa [he] using hm a (ball_subset_closedBall ha)
    rw [hillFilledFreeGapUnit,if_neg hE,
      hillLocalGapPolynomial_eq_of_pair 0 h0q h0r k hk p hboundary ha hb hm,
      twoZeroQuotient_factor _ a b haz hbz hab E]
    exact mul_div_cancel_left₀ _ (mul_ne_zero haE hbE)

end NLS.KdV
