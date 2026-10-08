import NLS.Fourier.PeriodOneCoefficients
import NLS.Fourier.CubicNLS

/-! # Pointwise algebra of absolutely convergent period-one Fourier series -/
noncomputable section
open Complex
open scoped ComplexConjugate
namespace NLS.Fourier

/-- Period-one synthesis as a bounded map into the uniform norm on the circle. -/
def periodOneSynthesisCLM : Coeff 1 →L[ℂ] C(AddCircle (2 : ℝ), ℂ) :=
  continuousSynthesisCLM.comp (Coeff.periodDouble (p := 1)).toContinuousLinearMap

@[simp] theorem periodOneSynthesisCLM_apply (a : Coeff 1) (x : ℝ) :
    periodOneSynthesisCLM a (x : AddCircle (2 : ℝ)) = periodOneSynthesis a x := rfl

@[simp] theorem periodOneSynthesis_add (a b : Coeff 1) (x : ℝ) :
    periodOneSynthesis (a+b) x = periodOneSynthesis a x+periodOneSynthesis b x := by
  change periodOneSynthesisCLM (a+b) (x : AddCircle (2 : ℝ)) = _
  rw [map_add]
  rfl

@[simp] theorem periodOneSynthesis_smul (c : ℂ) (a : Coeff 1) (x : ℝ) :
    periodOneSynthesis (c • a) x = c*periodOneSynthesis a x := by
  change periodOneSynthesisCLM (c • a) (x : AddCircle (2 : ℝ)) = _
  rw [map_smul]
  rfl

/-- Translating original coefficients multiplies by the period-one Fourier wave. -/
theorem periodOneSynthesis_shift (a : Coeff 1) (k : ℤ) (x : ℝ) :
    periodOneSynthesis (Coeff.shift k a) x = wave (2*k) x*periodOneSynthesis a x := by
  calc
    _ = ∑' n : ℤ, a n*wave (2*(n+k)) x := by
      rw [periodOneSynthesis_eq_tsum,
        ← (Equiv.addRight k).tsum_eq (fun n : ℤ => Coeff.shift k a n*wave (2*n) x)]
      apply tsum_congr
      intro n
      change a (n+k-k)*wave (2*(n+k)) x = _
      rw [add_sub_cancel_right]
    _ = (∑' n : ℤ, a n*wave (2*n) x)*wave (2*k) x := by
      simp_rw [mul_add,wave_add,← mul_assoc]
      rw [tsum_mul_right]
    _ = _ := by rw [periodOneSynthesis_eq_tsum]; ring

/-- The actual absolutely convergent convolution synthesizes to pointwise multiplication. -/
theorem periodOneSynthesis_convolution (a b : Coeff 1) (x : ℝ) :
    periodOneSynthesis (Coeff.convolution a b) x = periodOneSynthesis a x*periodOneSynthesis b x := by
  let L : Coeff 1 →L[ℂ] ℂ := (ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))).comp periodOneSynthesisCLM
  change L (Coeff.convolution a b) = _
  rw [Coeff.convolution,ContinuousLinearMap.map_tsum _ (Coeff.summable_convolution_terms a b)]
  have he (k : ℤ) : L (b k • Coeff.shift k a) = (b k*wave (2*k) x)*periodOneSynthesis a x := by
    change periodOneSynthesis (b k • Coeff.shift k a) x = _
    rw [periodOneSynthesis_smul,periodOneSynthesis_shift]
    ring
  simp_rw [he]
  rw [tsum_mul_right,← periodOneSynthesis_eq_tsum,mul_comm]

/-- Conjugate reflection is the actual complex conjugate of the physical Fourier series. -/
theorem periodOneSynthesis_conjugateReflection (a : Coeff 1) (x : ℝ) :
    periodOneSynthesis (star (Coeff.reflection a)) x = conj (periodOneSynthesis a x) := by
  rw [periodOneSynthesis_eq_tsum,periodOneSynthesis_eq_tsum,Complex.conj_tsum,
    ← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => (star (Coeff.reflection a)) n*wave (2*n) x)]
  apply tsum_congr
  intro n
  change conj (a (-(-n)))*wave (2*(-n)) x = conj (a n*wave (2*n) x)
  simp only [neg_neg,mul_neg,wave_neg,map_mul]

/-- The weighted cubic field synthesizes to the physical cubic nonlinearity,
with the defocusing NLS sign and the original period-one normalization. -/
theorem periodOneSynthesis_cubicNLS (w : SpectralWeight) (a : WeightedCoeff w.toWeight 1) (x : ℝ) :
    periodOneSynthesis (w.toCoeff (cubicNLS w a)) x =
      (-2*I)* (periodOneSynthesis (w.toCoeff a) x)^2*conj (periodOneSynthesis (w.toCoeff a) x) := by
  have hc : w.toCoeff (nlsConjugate w a) = star (Coeff.reflection (w.toCoeff a)) := by
    ext n
    simp [nlsConjugate_apply,Coeff.reflection_apply]
  rw [cubicNLS,map_smul,periodOneSynthesis_smul,w.toCoeff_convolution,w.toCoeff_convolution,
    periodOneSynthesis_convolution,periodOneSynthesis_convolution,hc,periodOneSynthesis_conjugateReflection]
  ring

end NLS.Fourier
