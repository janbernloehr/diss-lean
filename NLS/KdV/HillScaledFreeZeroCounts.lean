import NLS.KdV.HillScaledFreeContourGeometry
import NLS.KdV.HillAllGapMultiplicities
import NLS.KdV.HillFreeDirichlet
import NLS.KdV.HillDirichletSimplicity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillScaledFreeGapContour_zero_unique (ρ : ℝ) (hρ1 : ρ ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (E : ℂ)
    (hE : E ∈ closedBall (hillRealGapCenter 0 h0q h0r n : ℂ)
      (ρ*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n)))
    (hz : hillL2Radicand 0 E=0) : E=(hillRealGapCenter 0 h0q h0r n : ℂ) := by
  let R := hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n
  have hR : 0 ≤ R := (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r n hn).1
    (hillRealGapContour_geometry 0 h0q h0r n hn).2.1).le
  have hbig := closedBall_subset_closedBall (mul_le_of_le_one_left hR hρ1) hE
  have hfilled := hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r n hn hbig
  have he := hillL2Radicand_eq_gap_polynomial_mul_deflated_sq 0 h0q h0r n hn E hfilled
  obtain ⟨hl,hu⟩ := hillFreeGapEndpoints h0q h0r n hn
  rw [map_zero,hz,hl,hu] at he
  have hUne := pow_ne_zero 2 (hillDeflatedEnergyCanonicalRoot_ne_zero 0 h0q h0r n hn E hfilled)
  have hp := (mul_eq_zero.mp he.symm).resolve_right hUne
  have hEq : E=(freeHillValue n : ℂ) := sub_eq_zero.mp (mul_self_eq_zero.mp hp)
  simpa only [hillFreeGapCenter h0q h0r n hn] using hEq

theorem hillL2DirichletCharacteristic_free_zero_imp_radicand (E : ℂ)
    (hz : hillL2DirichletCharacteristic 0 E=0) : hillL2Radicand 0 E=0 := by
  have hE : E≠0 := by
    intro he
    rw [he,hillL2DirichletCharacteristic_free_zero] at hz
    exact one_ne_zero hz
  have hs : Complex.sqrt E≠0 := by
    intro he
    have hh := complex_sqrt_sq E
    rw [he,zero_pow (by norm_num : 2≠0)] at hh
    exact hE hh.symm
  have hd := hillL2DirichletCharacteristic_free_sq (Complex.sqrt E) hs
  rw [complex_sqrt_sq,hz] at hd
  have hsin : sin (Complex.sqrt E)=0 := (div_eq_zero_iff.mp hd.symm).resolve_right hs
  rw [hillL2Radicand_zero,hsin,zero_pow (by norm_num : 2≠0),mul_zero]

theorem hillScaledFreeGapContour_zero_counts (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) :
    analyticZeroCount (hillL2Radicand 0) (closedBall (hillRealGapCenter 0 h0q h0r n : ℂ)
      (ρ*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n))) = 2 ∧
    analyticZeroCount (hillL2DirichletCharacteristic 0) (closedBall (hillRealGapCenter 0 h0q h0r n : ℂ)
      (ρ*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n))) = 1 := by
  have hR : 0 < ρ*(hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n) :=
    mul_pos hρ (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r n hn).1
      (hillRealGapContour_geometry 0 h0q h0r n hn).2.1)
  constructor
  · rw [analyticZeroCount_eq_order_of_isolated _ _ _ hR.le
      (hillScaledFreeGapContour_zero_unique h0q h0r ρ hρ1 n hn),hillFreeGapCenter h0q h0r n hn]
    exact hillL2Radicand_free_order n hn
  · rw [analyticZeroCount_eq_order_of_isolated _ _ _ hR.le (fun E hE hz =>
      hillScaledFreeGapContour_zero_unique h0q h0r ρ hρ1 n hn E hE
        (hillL2DirichletCharacteristic_free_zero_imp_radicand E hz))]
    apply analyticOrderNatAt_hillL2Dirichlet_zero 0 (by simpa only [map_zero] using h0r)
    rw [hillFreeGapCenter h0q h0r n hn]
    have he : (freeHillValue n : ℂ)=((n : ℂ)*Real.pi)^2 := by
      simp only [freeHillValue,Int.cast_natCast,ofReal_mul,ofReal_pow,ofReal_natCast]
      ring
    rw [he]
    exact hillL2DirichletCharacteristic_free_nat_root n hn

end NLS.KdV
