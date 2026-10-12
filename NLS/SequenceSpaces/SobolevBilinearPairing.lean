import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.Reflection

/-! # Physical bilinear pairing on the full real Sobolev scale

The scalar distributional pairing uses opposite Fourier indices. Reciprocal
Sobolev weights cancel, giving the exact Hölder bound for every conjugate
Banach pair, including either infinity endpoint.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The corrected scalar bilinear pairing as a bounded bilinear map. -/
def sobolevBilinearPairing (s : ℝ) :
    WeightedCoeff (Weight.sobolev s) p →L[ℂ]
      WeightedCoeff (Weight.sobolev (-s)) q →L[ℂ] ℂ :=
  (((Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap).comp
    (weightIsometry (Weight.sobolev (-s)) q).toContinuousLinearEquiv.toContinuousLinearMap).precomp ℂ).comp
      (Coeff.dualPairing.comp
        (weightIsometry (Weight.sobolev s) p).toContinuousLinearEquiv.toContinuousLinearMap)

omit [Fact (1 ≤ p)] [p.HolderConjugate q] in
private theorem sobolev_pair_term (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) (n : ℤ) :
    weightEquiv (Weight.sobolev s) p a n *
      Coeff.reflection (weightEquiv (Weight.sobolev (-s)) q b) n = a.val n*b.val (-n) := by
  simp only [Coeff.reflection_apply,weightEquiv_apply,Weight.sobolev_neg]
  have hw : (Weight.sobolev s n : ℂ)*(Weight.sobolev (-s) n : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have hx : 0 < 1+|(n : ℝ)| := by positivity
    simp [Weight.sobolev_apply,Real.rpow_neg hx.le,ne_of_gt (Real.rpow_pos_of_pos hx s)]
  calc
    _ = ((Weight.sobolev s n : ℂ)*(Weight.sobolev (-s) n : ℂ))*(a.val n*b.val (-n)) := by ring
    _ = _ := by rw [hw,one_mul]

/-- Opposite indices, with no complex conjugation and no change of normalization. -/
theorem sobolevBilinearPairing_apply (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    sobolevBilinearPairing s a b = ∑' n : ℤ, a.val n*b.val (-n) := by
  change Coeff.dualPairing (weightEquiv _ _ a) (Coeff.reflection (weightEquiv _ _ b)) = _
  rw [Coeff.dualPairing_apply]
  exact tsum_congr (sobolev_pair_term s a b)

/-- Absolute convergence at every conjugate endpoint on the full real Sobolev scale. -/
theorem summable_norm_sobolevBilinearPairing (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    Summable (fun n : ℤ => ‖a.val n*b.val (-n)‖) := by
  simpa only [sobolev_pair_term] using
    Coeff.summable_norm_dualPairing (weightEquiv _ _ a) (Coeff.reflection (weightEquiv _ _ b))

/-- The bound retains the exact product of the original weighted norms. -/
theorem norm_sobolevBilinearPairing_le (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    ‖sobolevBilinearPairing s a b‖ ≤ ‖a‖*‖b‖ := by
  change ‖Coeff.dualPairing (weightEquiv _ _ a) (Coeff.reflection (weightEquiv _ _ b))‖ ≤ _
  simpa only [LinearIsometryEquiv.norm_map,← norm_eq] using
    Coeff.norm_dualPairing_le (weightEquiv _ _ a) (Coeff.reflection (weightEquiv _ _ b))

end NLS.WeightedCoeff
