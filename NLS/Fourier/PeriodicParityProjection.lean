import NLS.Fourier.PeriodicSobolevDuality
import NLS.Fourier.SobolevSynthesis
import NLS.SequenceSpaces.Parity

/-! The same bounded parity mask on original distributions and physical
periodic L2 functions, retaining every original raw Fourier coefficient. -/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier
open SmoothPeriodicTest PeriodicFourierLebesgue

/-- Parity projection on every original Fourier-Lebesgue distribution space. -/
def periodicParityProjection {L : ℝ} [Fact (0 < L)] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (r : ℤ) :
    FourierLebesgueSpace L s p →L[ℂ] FourierLebesgueSpace L s p :=
  (sobolevCoefficients s p).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.parityProjection (Weight.sobolev s) r).comp
      (sobolevCoefficients s p).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Original distribution coefficients are masked in their original slots. -/
theorem periodicParityProjection_coefficient {L : ℝ} [Fact (0 < L)] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (r : ℤ) (f : FourierLebesgueSpace L s p) (k : ℤ) :
    (periodicParityProjection s p r f).val (mode (-k)) = if k%2=r%2 then f.val (mode (-k)) else 0 := by
  change ((sobolevCoefficients s p) ((sobolevCoefficients s p).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact WeightedCoeff.parityProjection_apply (Weight.sobolev s) r (sobolevCoefficients s p f) k

/-- The parity projection is idempotent on the ENTIRE original space. -/
theorem periodicParityProjection_idempotent {L : ℝ} [Fact (0 < L)] (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (r : ℤ) (f : FourierLebesgueSpace L s p) : periodicParityProjection s p r (periodicParityProjection s p r f)=periodicParityProjection s p r f := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [periodicParityProjection_coefficient,periodicParityProjection_coefficient]
  split_ifs <;> rfl

/-- The physical periodic L2 parity projector on ALL Hilbert inputs. -/
def circleL2ParityProjection (r : ℤ) : CircleL2 →L[ℂ] CircleL2 :=
  l2Synthesis.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Coeff.parityProjection r).comp l2Synthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Its actual physical Fourier coefficient is the same literal parity mask. -/
theorem circleL2ParityProjection_coefficient (r : ℤ) (F : CircleL2) (k : ℤ) :
    fourierCoeff (circleL2ParityProjection r F) k=if k%2=r%2 then fourierCoeff F k else 0 := by
  change fourierCoeff (l2Synthesis (Coeff.parityProjection r (l2Synthesis.symm F))) k = _
  rw [fourierCoeff_l2Synthesis,Coeff.parityProjection_apply]
  change (if k%2=r%2 then fourierBasis.repr F k else 0)=_
  rw [fourierBasis_repr]

/-- Physical parity projection is contractive in the exact source L2 norm. -/
theorem norm_circleL2ParityProjection_le (r : ℤ) (F : CircleL2) : ‖circleL2ParityProjection r F‖ ≤ ‖F‖ := by
  change ‖l2Synthesis (Coeff.parityProjection r (l2Synthesis.symm F))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact (Coeff.norm_parityProjection_apply_le r _).trans_eq (l2Synthesis.symm.norm_map F)

end NLS.Fourier
