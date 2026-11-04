import NLS.KdV.HillComplexGapQuadraticRoot
import NLS.KdV.HillFilledFreeGapRoot
import NLS.KdV.HillFreeGapQuotient

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillLocalGapPolynomial_free (k : ℕ) (hk : 1 ≤ k) (E : ℂ) :
    hillLocalGapPolynomial 0 h0q h0r k 0 E=(E-(hillRealGapCenter 0 h0q h0r k : ℂ))^2 := by
  have hR := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  obtain ⟨_,_,hb,hm⟩ := hillFreeGap_two_zero_data h0q h0r k hk
  have h := hillLocalGapPolynomial_eq_of_pair 0 h0q h0r k hk 0 hb (mem_ball_self hR) (mem_ball_self hR) hm E
  simpa only [pow_two] using h

theorem hillFreeGapQuadraticRoot_base (k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E≠(hillRealGapCenter 0 h0q h0r k : ℂ)) :
    hillFreeGapQuadraticRoot h0q h0r k (E,0)=(hillRealGapCenter 0 h0q h0r k : ℂ)-E := by
  rw [hillFreeGapQuadraticRoot,hillLocalGapPolynomial_free h0q h0r k hk E,
    div_self (pow_ne_zero 2 (sub_ne_zero.mpr hE)),sqrt_one,mul_one]

theorem hillFilledFreeGapRoot_base (k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) :
    hillFilledFreeGapRoot h0q h0r k (E,0)=hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E := by
  have hn := hillDeflatedEnergyCanonicalRoot_ne_zero 0 h0q h0r k hk E
    (hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r k hk hE)
  rw [hillFilledFreeGapRoot,hillFilledFreeGapUnit_zero_eq_physical_sq h0q h0r k hk E hE,
    div_self (pow_ne_zero 2 hn),sqrt_one,mul_one]

theorem hillFreeGap_root_product_base (k : ℕ) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) :
    hillFreeGapQuadraticRoot h0q h0r k (E,0)*hillFilledFreeGapRoot h0q h0r k (E,0)=
      hillEnergyCanonicalRootProduct 0 h0q h0r E := by
  have hR := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  have hEc : E≠(hillRealGapCenter 0 h0q h0r k : ℂ) := by
    intro he
    have hh : dist E (hillRealGapCenter 0 h0q h0r k : ℂ)=
      hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k := hE
    rw [he,dist_self] at hh
    linarith
  rw [hillFreeGapQuadraticRoot_base h0q h0r k hk E hEc,
    hillFilledFreeGapRoot_base h0q h0r k hk E (sphere_subset_closedBall hE),
    hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated 0 h0q h0r k hk E]
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r k hk
  rw [hl,hu,← hillFreeGapCenter h0q h0r k hk]
  congr 1
  simp only [endpointRoot,normalizedStandardRoot,sub_self,zero_pow (by norm_num : 2≠0),
    zero_div,sub_zero,sqrt_one,mul_one]
  ring

end NLS.KdV
