import NLS.SequenceSpaces.NegativeSpectralWeight

/-! # Fourier modulation in signed spectral weights

The positive-weight modulation construction extends to the source's signed
weights using the already proved comparison with translated weights.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reindexing a translated arbitrary positive weight is an isometry. -/
def shiftWeightIsometry (w : Weight) (i : ℤ) :
    WeightedCoeff (w.shift i) p ≃ₗᵢ[ℂ] WeightedCoeff w p :=
  ((weightIsometry _ p).trans (Coeff.shift i)).trans (weightIsometry _ p).symm

@[simp] theorem shiftWeightIsometry_apply (w : Weight) (i : ℤ)
    (a : WeightedCoeff (w.shift i) p) (n : ℤ) :
    (shiftWeightIsometry w i a).val n = a.val (n-i) := by
  change (w.shift i (n-i):ℂ)*a.val (n-i)/(w n:ℂ) = _
  simp only [Weight.shift_apply, sub_add_cancel]
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero n)

end NLS.WeightedCoeff
namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual Fourier modulation on every signed source weighted space. -/
def negativeModulation (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (i : ℤ) :
    WeightedCoeff (w.negativeSobolev r) p ≃L[ℂ] WeightedCoeff (w.negativeSobolev r) p :=
  (w.negativeShiftEquiv r hr i p).trans
    (WeightedCoeff.shiftWeightIsometry (w.negativeSobolev r) i).toContinuousLinearEquiv

@[simp] theorem negativeModulation_apply (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (i : ℤ)
    (a : WeightedCoeff (w.negativeSobolev r) p) (n : ℤ) :
    (w.negativeModulation r hr i a).val n = a.val (n-i) := by
  change (WeightedCoeff.shiftWeightIsometry _ i (w.negativeShiftEquiv r hr i p a)).val n = _
  rw [WeightedCoeff.shiftWeightIsometry_apply, negativeShiftEquiv_apply]

/-- The signed Sobolev factor in the modulation bound has positive order. -/
theorem norm_negativeModulation_le (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (i : ℤ)
    (a : WeightedCoeff (w.negativeSobolev r) p) :
    ‖w.negativeModulation r hr i a‖ ≤ (w i*Weight.sobolev r i)*‖a‖ := by
  change ‖WeightedCoeff.shiftWeightIsometry _ i (w.negativeShiftEquiv r hr i p a)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact WeightComparison.norm_map_le _ _ _
    (mul_nonneg (w.positive i).le ((Weight.sobolev r).positive i).le)
    (fun k => w.negativeSobolev_shift_le r hr i k) a

/-- Shifting the norm opposite to an actual Fourier modulation recovers the
original norm exactly, for every signed source weight and Banach exponent. -/
theorem negativeShiftedNorm_negativeModulation (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r)
    (i : ℤ) (a : WeightedCoeff (w.negativeSobolev r) p) :
    w.negativeShiftedNorm r hr (-i) p (w.negativeModulation r hr i a) = ‖a‖ := by
  have he : WeightedCoeff.weightEquiv ((w.negativeSobolev r).shift (-i)) p
      (w.negativeShiftEquiv r hr (-i) p (w.negativeModulation r hr i a)) =
        Coeff.shift i (WeightedCoeff.weightEquiv (w.negativeSobolev r) p a) := by
    ext k
    simp only [WeightedCoeff.weightEquiv_apply, negativeShiftEquiv_apply, negativeModulation_apply,
      Weight.shift_apply, Coeff.shift_apply, sub_eq_add_neg]
  change ‖WeightedCoeff.weightEquiv ((w.negativeSobolev r).shift (-i)) p
    (w.negativeShiftEquiv r hr (-i) p (w.negativeModulation r hr i a))‖ = ‖a‖
  rw [he, Coeff.norm_shift]
  rfl

end NLS.SpectralWeight
