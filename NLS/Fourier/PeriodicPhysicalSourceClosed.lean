import NLS.Fourier.PeriodicSobolevDuality
import NLS.Fourier.RealMeanZeroPeriodOne
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-!
# Closed physical source constraints in every original Sobolev Fourier norm

Reality, mean zero and physical period one are imposed on the entire
original distribution. Their exact normalized Fourier characterization
makes the physical locus closed at every real order and Banach exponent.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest

/-- Every original Fourier coefficient is continuous in the original norm. -/
theorem continuous_originalSobolevCoefficient (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :
    Continuous (fun q : FourierLebesgueSpace (2:ℝ) s p => q.val (mode n)) := by
  simpa only [Function.comp_def,WeightedCoeff.evalCLM_apply,sobolevCoefficients_apply,neg_neg] using
    (WeightedCoeff.evalCLM (Weight.sobolev s) p (-n)).continuous.comp
      (sobolevCoefficients (L := 2) s p).continuous

/-- The entire physical real mean-zero period-one locus is norm closed
in every original period-two Fourier-Lebesgue space. -/
theorem isClosed_realMeanZeroPeriodOneSource (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsClosed {q : FourierLebesgueSpace (2:ℝ) s p | q.val.IsRealMeanZeroPeriodOne} := by
  have he : {q : FourierLebesgueSpace (2:ℝ) s p | q.val.IsRealMeanZeroPeriodOne} =
      {q | q.val (mode 0) = 0} ∩
        ((⋂ n : ℤ, {q | q.val (mode n) = star (q.val (mode (-n)))}) ∩
          ⋂ k : ℤ, {q | q.val (mode (-(2*k+1))) = 0}) := by
    ext q
    simp only [mem_ofPred_eq,mem_inter_iff,mem_iInter]
    exact Distribution.isRealMeanZeroPeriodOne_iff_coefficients q.val
  rw [he]
  exact (isClosed_eq (continuous_originalSobolevCoefficient s p 0) continuous_const).inter
    ((isClosed_iInter fun n => isClosed_eq (continuous_originalSobolevCoefficient s p n)
      (continuous_originalSobolevCoefficient s p (-n)).star).inter
        (isClosed_iInter fun k => isClosed_eq
          (continuous_originalSobolevCoefficient s p (-(2*k+1))) continuous_const))

end NLS.Fourier.PeriodicFourierLebesgue
