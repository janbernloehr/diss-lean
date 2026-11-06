import NLS.KdV.HillDeflatedCanonicalRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem hillOmittedEnergyRootFactor_im_eq_zero_on_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)))
    (k : ℕ) : (hillOmittedEnergyRootFactor q hq hr n k x).im = 0 := by
  unfold hillOmittedEnergyRootFactor
  split_ifs with hk
  · exact Complex.one_im
  · have horder := monotone_hillRealLabels q hq hr (by omega : 2*(k+1)-1 ≤ 2*(k+1))
    have hi : (endpointRoot (hillRealLabels q hq hr (2*(k+1)-1))
        (hillRealLabels q hq hr (2*(k+1))) x).im = 0 := by
      rcases hillRealGap_exterior_to_other_gap q hq hr n (k+1) hn (by omega) hk x hx with hl | hu
      · exact (endpointRoot_real_left _ _ x horder hl).2
      · exact (endpointRoot_real_right _ _ x horder hu).2
    have he : endpointRoot (hillRealLabels q hq hr (2*(k+1)-1))
        (hillRealLabels q hq hr (2*(k+1))) x =
        ((endpointRoot (hillRealLabels q hq hr (2*(k+1)-1))
          (hillRealLabels q hq hr (2*(k+1))) x).re : ℂ) := by
      apply Complex.ext <;> simp [hi]
    rw [hillEnergyRootFactor,he,← ofReal_div]
    exact Complex.ofReal_im _

theorem hillOmittedEnergyRootProduct_im_eq_zero_on_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    (hillOmittedEnergyRootProduct q hq hr n x).im = 0 := by
  have hf (k : ℕ) : conj (hillOmittedEnergyRootFactor q hq hr n k x) =
      hillOmittedEnergyRootFactor q hq hr n k x := by
    apply Complex.ext <;> simp [hillOmittedEnergyRootFactor_im_eq_zero_on_gap q hq hr n hn x hx k]
  have he := (multipliable_hillOmittedEnergyRootFactors q hq hr n x).map_tprod
    (starRingEnd ℂ) continuous_star
  change conj (∏' k : ℕ, hillOmittedEnergyRootFactor q hq hr n k x) =
    ∏' k : ℕ, conj (hillOmittedEnergyRootFactor q hq hr n k x) at he
  have hc : conj (hillOmittedEnergyRootProduct q hq hr n x) =
      hillOmittedEnergyRootProduct q hq hr n x := by
    rw [hillOmittedEnergyRootProduct,he]
    exact tprod_congr hf
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

theorem hillDeflatedEnergyCanonicalRoot_re_eq_zero_on_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    (hillDeflatedEnergyCanonicalRoot q hq hr n x).re = 0 := by
  have hx0 : hillRealLabels q hq hr 0 < x := by
    have hb := hillRealLabels_band_strict q hq hr 0
    simp only [mul_zero,zero_add] at hb
    exact hb.trans_le ((monotone_hillRealLabels q hq hr (by omega)).trans hx.1)
  have hs : Complex.sqrt ((x:ℂ)-hillRealLabels q hq hr 0) =
      (Real.sqrt (x-hillRealLabels q hq hr 0) : ℂ) := by
    rw [← ofReal_sub,Complex.sqrt_of_nonneg
      (by exact_mod_cast (show 0 ≤ x-hillRealLabels q hq hr 0 by linarith))]
    simp only [ofReal_re]
  have hi := hillOmittedEnergyRootProduct_im_eq_zero_on_gap q hq hr n hn x hx
  simp [hillDeflatedEnergyCanonicalRoot,hs,Complex.mul_re,Complex.mul_im,
    Complex.div_re,Complex.div_im,hi]

theorem im_I_mul_div_hillDeflatedEnergyCanonicalRoot_eq_zero_on_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)))
    (N : ℂ) (hN : N.im = 0) :
    (I*(N/hillDeflatedEnergyCanonicalRoot q hq hr n x)).im = 0 := by
  simp [Complex.mul_im,Complex.div_re,hN,
    hillDeflatedEnergyCanonicalRoot_re_eq_zero_on_gap q hq hr n hn x hx]

end NLS.KdV
