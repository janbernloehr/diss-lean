import NLS.KdV.HillBoundedComplexTailPeriodControl
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

/-- An actual unscaled own-period error bound; unlike the mixed scaled
estimate it remains informative at the own differential index. -/
theorem norm_hillAbelianComplexOwnPeriod_sub_free_le
    (n : ℕ) (hn : 1≤n) (a p : Coeff 2) (C : ℝ)
    (hdom : ∀ E∈sphere (hillRealGapCenter 0 h0q h0r n : ℂ)
      (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n),
      (E,p)∈hillAbelianComplexRootDomain 0 h0q h0r)
    (hbound : ∀ E∈sphere (hillRealGapCenter 0 h0q h0r n : ℂ)
      (hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n),
      ‖hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)-1‖≤C*‖p‖/(n : ℝ)) :
    ‖hillAbelianComplexPeriod 0 h0q h0r n n (a,p)-hillAbelianHilbertPeriod 0 h0q h0r n n a‖≤
      2*C*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(n : ℝ) := by
  let R := hillRealGapHalfLength 0 h0q h0r n+hillRealGapCollar 0 h0q h0r n
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r n hn).1
    (hillRealGapContour_geometry 0 h0q h0r n hn).2.1
  have hi (E : ℂ) (hE : E∈sphere (hillRealGapCenter 0 h0q h0r n : ℂ) R) :
      ‖(1 : ℂ)*(hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 h0q h0r (E,p)-
        hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E)‖≤
        (2/R)*Real.exp ((8/Real.pi^2)*‖a‖)*(C*‖p‖/(n : ℝ)) := by
    have hfree : ‖hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E‖≤
        (2/R)*Real.exp ((8/Real.pi^2)*‖a‖) := by
      rw [hillAbelianHilbertPsi_contour_separation h0q h0r n n hn E hE a,mul_div_right_comm,norm_mul]
      exact mul_le_mul (norm_hillFreeOwnAbelianQuotient_on_contour h0q h0r n hn E hE)
        (norm_hilbertWeightedProduct_hillFreeContour_le h0q h0r n n hn E hE a) (norm_nonneg _) (by positivity)
    have hd0 := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain 0 h0q h0r E (hdom E hE).1.1
    have hdc := hillAbelianComplexRoot_ne_zero 0 h0q h0r (E,p) (hdom E hE)
    have he : hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 h0q h0r (E,p)-
        hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E=
        (hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E)*
          (hillEnergyCanonicalRootProduct 0 h0q h0r E/hillAbelianComplexRoot 0 h0q h0r (E,p)-1) := by
      field_simp
    rw [one_mul,he,norm_mul]
    exact mul_le_mul hfree (hbound E hE) (norm_nonneg _) (by positivity)
  have hh := norm_normalized_circleIntegral_difference_le
    (fun E => hillAbelianHilbertPsi n (E,a)/hillAbelianComplexRoot 0 h0q h0r (E,p))
    (fun E => hillAbelianHilbertPsi n (E,a)/hillEnergyCanonicalRootProduct 0 h0q h0r E)
    (hillRealGapCenter 0 h0q h0r n : ℂ) 1 R
    ((2/R)*Real.exp ((8/Real.pi^2)*‖a‖)*(C*‖p‖/(n : ℝ))) hR.le
    (hillAbelianComplexIntegrand_circleIntegrable h0q h0r n n hn a p hdom)
    (hillAbelianHilbertIntegrand_circleIntegrable h0q h0r n n hn a) hi
  rw [one_mul] at hh
  apply hh.trans_eq
  field_simp

/-- On any bounded complex potential ball, all sufficiently high own
normalization periods have the original O(1/n) complex-minus-free error. -/
theorem exists_hillAbelianComplexOwnPeriod_bounded_tail_error (B : ℝ) :
    ∃ J : ℕ, ∃ C : ℝ, 1≤J ∧ 0<C ∧ ∀ p : Coeff 2, ‖p‖≤B →
      ∀ n : ℕ, J≤n → ∀ a : Coeff 2,
      ‖hillAbelianComplexPeriod 0 h0q h0r n n (a,p)-hillAbelianHilbertPeriod 0 h0q h0r n n a‖≤
        C*Real.exp ((8/Real.pi^2)*‖a‖)*‖p‖/(n : ℝ) := by
  obtain ⟨J,hJ,C,hC,hbound⟩ := exists_hillFreeGapContour_bounded_complex_tail_inverse_bound h0q h0r B
  refine ⟨J,2*C,hJ,by positivity,?_⟩
  intro p hp n hn a
  exact norm_hillAbelianComplexOwnPeriod_sub_free_le h0q h0r n (hJ.trans hn) a p C
    (fun E hE => (hbound p hp n hn E hE).1) (fun E hE => (hbound p hp n hn E hE).2)

end NLS.KdV
