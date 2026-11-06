import NLS.KdV.HillContourHilbertPsiBounds
import NLS.KdV.HillUniformComplexOwnPeriods

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem norm_hillFreeRoot_div_complexRoot_le_of_tail_error
    (k : ℕ) (hk : 1≤k) (E : ℂ) (p : Coeff 2) (C : ℝ) (hC : 0≤C)
    (hb : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)-1‖≤C*‖p‖/(k : ℝ)) :
    ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤1+C*‖p‖ := by
  have hkR : (1 : ℝ)≤k := by exact_mod_cast hk
  have hh := norm_le_norm_sub_add (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)) 1
  rw [norm_one] at hh
  have hd := div_le_self (mul_nonneg hC (norm_nonneg p)) hkR
  linarith

/-- Own high-contour control for any genuine normalization denominator
bounded below by c, without a small-potential assumption. -/
theorem norm_hillAbelianHilbertPsi_normalized_own_root_le
    (n : ℕ) (hn : 1≤n) (a p : Coeff 2) (d : ℂ) (c C : ℝ) (hc : 0<c) (hC : 0≤C)
    (hd : c≤‖d‖) (E : ℂ)
    (hE : E∈sphere (hillRealGapCenter 0 h0q h0r n : ℂ)
      (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n))
    (hdom : (E,p)∈hillAbelianComplexRootDomain 0 h0q h0r)
    (hb : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)-1‖≤C*‖p‖/(n : ℝ)) :
    ‖(hillAbelianHilbertPsi n (E,a)/d)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤
      (2*Real.exp ((8/Real.pi^2)*‖a‖)*(1+C*‖p‖)/c)/
        (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n) := by
  let R := hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r n hn).1
    (hillRealGapContour_geometry 0 h0q h0r n hn).2.1
  have hr := norm_hillFreeRoot_div_complexRoot_le_of_tail_error h0q h0r n hn E p C hC hb
  have hfree : ‖hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E‖≤
      (2/R)*Real.exp ((8/Real.pi^2)*‖a‖) := by
    rw [hillAbelianHilbertPsi_contour_separation h0q h0r n n hn E hE a,mul_div_right_comm,norm_mul]
    exact mul_le_mul (norm_hillFreeOwnAbelianQuotient_on_contour h0q h0r n hn E hE)
      (norm_hilbertWeightedProduct_hillFreeContour_le h0q h0r n n hn E hE a) (norm_nonneg _) (by positivity)
  have hf0 := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 h0q h0r E hdom.1.1
  have he : (hillAbelianHilbertPsi n (E,a)/d)/hillAbelianComplexRoot 0 h0q h0r (E,p)=
      ((hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E)*
        (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)))/d := by
    field_simp
  rw [he,norm_div,norm_mul]
  apply (div_le_div₀ (by positivity : 0≤(2/R)*Real.exp ((8/Real.pi^2)*‖a‖)*(1+C*‖p‖))
    (mul_le_mul hfree hr (norm_nonneg _) (by positivity)) hc hd).trans_eq
  ring

/-- The original off-diagonal scaled kernel bound, with any genuine
own normalization bounded below by c on a bounded source set. -/
theorem norm_scaled_hillAbelianHilbertPsi_normalized_root_le
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (hnk : n≠k)
    (a p : Coeff 2) (d : ℂ) (c C : ℝ) (hc : 0<c) (hC : 0≤C) (hd : c≤‖d‖) (E : ℂ)
    (hE : E∈sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k))
    (hdom : (E,p)∈hillAbelianComplexRootDomain 0 h0q h0r)
    (hb : ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)-1‖≤C*‖p‖/(k : ℝ)) :
    ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      ((hillAbelianHilbertPsi n (E,a)/d)/hillAbelianComplexRoot 0 h0q h0r (E,p))‖≤
      (4*Real.exp ((8/Real.pi^2)*‖a‖)*(1+C*‖p‖)/c)/(k : ℝ) := by
  have hr := norm_hillFreeRoot_div_complexRoot_le_of_tail_error h0q h0r k hk E p C hC hb
  have hf0 := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 h0q h0r E hdom.1.1
  have he : (((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
      ((hillAbelianHilbertPsi n (E,a)/d)/hillAbelianComplexRoot 0 h0q h0r (E,p))=
      (((((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
        (hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E))*
          (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)))/d := by
    field_simp
  rw [he,norm_div,norm_mul]
  apply (div_le_div₀ (by positivity : 0≤(4/(k : ℝ))*Real.exp ((8/Real.pi^2)*‖a‖)*(1+C*‖p‖))
    (mul_le_mul (norm_scaled_hillAbelianHilbertPsi_free_root_le h0q h0r n k hn hk hnk E hE a) hr
      (norm_nonneg _) (by positivity)) hc hd).trans_eq
  ring

end NLS.KdV
