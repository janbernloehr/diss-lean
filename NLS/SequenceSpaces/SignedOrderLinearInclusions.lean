import NLS.SequenceSpaces.SignedOrderHalfFourierEquiv

/-! Complex coefficient-preserving signed order inclusions and the
original free half-Fourier map on unweighted Banach sequences. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

def signedOrderInclusion (s t : ℝ) (hst : s ≤ t) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    WeightedCoeff (Weight.signedSobolev t) p →L[ℂ] WeightedCoeff (Weight.signedSobolev s) p :=
  inclusionCLM _ _ (by
    intro k
    exact Real.rpow_le_rpow_of_exponent_le (le_max_left (1 : ℝ) |(k : ℝ)|) hst)

theorem signedOrderInclusion_apply (s t : ℝ) (hst : s ≤ t) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : WeightedCoeff (Weight.signedSobolev t) p) (k : ℤ) :
    (signedOrderInclusion s t hst p a).val k = a.val k := inclusionCLM_apply _ _ _ a k

def l2FreeHalfFourier : Coeff 2 →L[ℂ] WeightedCoeff (Weight.signedSobolev (1/2)) 2 :=
  (weightedMultiplierCLM Weight.one (Weight.signedSobolev (1/2)) halfFourierSymbol
    (1 / Real.sqrt (2 * Real.pi)) (by positivity) (by
      intro k
      simpa only [zero_add,Weight.signedSobolev,Real.rpow_zero,Weight.one_apply,mul_one] using
        halfFourierSymbol_signed_order_bound 0 k)).comp
      (weightIsometry Weight.one 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem l2FreeHalfFourier_apply (q : Coeff 2) (k : ℤ) :
    (l2FreeHalfFourier q).val k = halfFourierSymbol k * q k := by
  change halfFourierSymbol k * (q k / (Weight.one k : ℂ)) = _
  simp only [Weight.one_apply,ofReal_one,div_one]

end NLS.WeightedCoeff
