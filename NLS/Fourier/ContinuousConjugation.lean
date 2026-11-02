import NLS.Fourier.ContinuousSynthesis
import NLS.SequenceSpaces.Reflection

/-! # Physical conjugation of continuous Fourier data

Complex conjugation of the actual function is conjugate reflection of
its Fourier coefficients. This is not coefficientwise reality.
-/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace NLS.Fourier

theorem continuousFourierCLM_star (Q : C(AddCircle (2 : ℝ), ℂ)) :
    continuousFourierCLM (star Q) = star (Coeff.reflection (continuousFourierCLM Q)) := by
  ext k
  simp only [continuousFourierCLM_apply,lp.star_apply,Coeff.reflection_apply]
  change fourierCoeff (fun x => conj (Q x)) k = conj (fourierCoeff Q (-k))
  simp only [fourierCoeff,neg_neg,smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_mul,← fourier_neg]

end NLS.Fourier
