import NLS.ZakharovShabat.FloquetPeriodicFactor
import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Absolute continuity and derivatives of normalized Floquet modes -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.ZakharovShabat
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The compensating scalar exponential is smooth on the full real line. -/
theorem contDiff_floquetCompensatingExponential (μ : ℂ) :
    ContDiff ℝ 1 (fun t : ℝ => Complex.exp (-(t : ℂ)*Complex.log μ)) :=
  (Complex.ofRealCLM.contDiff.neg.mul contDiff_const).cexp

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
/-- Normalization preserves absolute continuity on every compact interval. -/
theorem absolutelyContinuousOnInterval_floquetPeriodicFactor (μ : ℂ) (F : ℝ → E)
    (a b : ℝ) (hF : AbsolutelyContinuousOnInterval F a b) :
    AbsolutelyContinuousOnInterval (floquetPeriodicFactor μ F) a b :=
  (contDiff_floquetCompensatingExponential μ).contDiffOn.absolutelyContinuousOnInterval.smul hF

/-- The scalar exponential has exactly the logarithmic correction derivative. -/
theorem hasDerivAt_floquetCompensatingExponential (μ : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ)*Complex.log μ))
      (-Complex.log μ * Complex.exp (-(t : ℂ)*Complex.log μ)) t := by
  simpa only [Function.comp_def,Pi.neg_apply,Complex.ofRealCLM_apply,Complex.ofReal_one,neg_mul,one_mul,smul_eq_mul] using!
    (Complex.hasDerivAt_exp (-(t : ℂ)*Complex.log μ)).scomp t
      (Complex.ofRealCLM.hasDerivAt.neg.mul_const (Complex.log μ))

/-- Removing the multiplier subtracts log(mu) times the normalized mode
from the derivative. -/
theorem hasDerivAt_floquetPeriodicFactor (μ : ℂ) (F : ℝ → E) (G : E) (t : ℝ)
    (hF : HasDerivAt F G t) :
    HasDerivAt (floquetPeriodicFactor μ F)
      (Complex.exp (-(t : ℂ)*Complex.log μ) • G - Complex.log μ • floquetPeriodicFactor μ F t) t := by
  convert! (hasDerivAt_floquetCompensatingExponential μ t).smul hF using 1
  dsimp [floquetPeriodicFactor]
  module

end NLS.ZakharovShabat
