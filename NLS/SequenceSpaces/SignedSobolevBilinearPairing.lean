import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.Reflection
import NLS.SequenceSpaces.SignedSobolevWeight

/-! # Physical bilinear pairing for the exact signed Sobolev weight

The scalar distributional pairing uses opposite Fourier indices. Reciprocal
signed weights cancel, giving the exact Hölder bound for every conjugate
Banach pair, including either infinity endpoint.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The opposite-index scalar bilinear pairing as a bounded bilinear map. -/
def signedSobolevBilinearPairing (s : ℝ) :
    WeightedCoeff (Weight.signedSobolev s) p →L[ℂ]
      WeightedCoeff (Weight.signedSobolev (-s)) q →L[ℂ] ℂ :=
  (((Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (weightIsometry (Weight.signedSobolev (-s)) q).toContinuousLinearEquiv.toContinuousLinearMap).precomp ℂ).comp
      (Coeff.dualPairing.comp
        (weightIsometry (Weight.signedSobolev s) p).toContinuousLinearEquiv.toContinuousLinearMap)

omit [Fact (1 ≤ p)] [p.HolderConjugate q] in
private theorem signedSobolev_pair_term (s : ℝ)
    (a : WeightedCoeff (Weight.signedSobolev s) p) (b : WeightedCoeff (Weight.signedSobolev (-s)) q) (n : ℤ) :
    weightEquiv (Weight.signedSobolev s) p a n *
      Coeff.reflection (weightEquiv (Weight.signedSobolev (-s)) q b) n = a.val n*b.val (-n) := by
  simp only [Coeff.reflection_apply,weightEquiv_apply,Weight.signedSobolev_neg]
  have hw : (Weight.signedSobolev s n : ℂ)*(Weight.signedSobolev (-s) n : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have hx : 0 < max 1 |(n : ℝ)| := by exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    simp [Weight.signedSobolev,Real.rpow_neg hx.le,ne_of_gt (Real.rpow_pos_of_pos hx s)]
  calc
    _ = ((Weight.signedSobolev s n : ℂ)*(Weight.signedSobolev (-s) n : ℂ))*(a.val n*b.val (-n)) := by ring
    _ = _ := by rw [hw,one_mul]

/-- Opposite indices, with no complex conjugation and no change of normalization. -/
theorem signedSobolevBilinearPairing_apply (s : ℝ)
    (a : WeightedCoeff (Weight.signedSobolev s) p) (b : WeightedCoeff (Weight.signedSobolev (-s)) q) :
    signedSobolevBilinearPairing s a b = ∑' n : ℤ, a.val n*b.val (-n) := by
  change Coeff.dualPairing (weightEquiv _ _ a) (Coeff.reflection (weightEquiv _ _ b)) = _
  rw [Coeff.dualPairing_apply]
  exact tsum_congr (signedSobolev_pair_term s a b)

/-- Absolute convergence at every conjugate endpoint on the full real Sobolev scale. -/
theorem summable_norm_signedSobolevBilinearPairing (s : ℝ)
    (a : WeightedCoeff (Weight.signedSobolev s) p) (b : WeightedCoeff (Weight.signedSobolev (-s)) q) :
    Summable (fun n : ℤ => ‖a.val n*b.val (-n)‖) := by
  simpa only [signedSobolev_pair_term] using
    Coeff.summable_norm_dualPairing (weightEquiv _ _ a) (Coeff.reflection (weightEquiv _ _ b))

/-- The bound retains the exact product of the original weighted norms. -/
theorem norm_signedSobolevBilinearPairing_le (s : ℝ)
    (a : WeightedCoeff (Weight.signedSobolev s) p) (b : WeightedCoeff (Weight.signedSobolev (-s)) q) :
    ‖signedSobolevBilinearPairing s a b‖ ≤ ‖a‖*‖b‖ := by
  change ‖Coeff.dualPairing (weightEquiv _ _ a) (Coeff.reflection (weightEquiv _ _ b))‖ ≤ _
  simpa only [LinearIsometryEquiv.norm_map,← norm_eq] using
    Coeff.norm_dualPairing_le (weightEquiv _ _ a) (Coeff.reflection (weightEquiv _ _ b))

end NLS.WeightedCoeff
