import NLS.SequenceSpaces.WeightedPhaseFlow
import NLS.SequenceSpaces.PeriodDoubling

/-! # Spatial translation of Fourier coefficients

The frequency scale is explicit: `π` for period two and `2π` for period one.
Translations are isometric equivalences, including on the derivative domain.
-/

noncomputable section
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translation for Fourier modes `exp (i c n x)`. -/
def Coeff.spatialTranslation (c t : ℝ) : Coeff p ≃ₗᵢ[ℂ] Coeff p where
  __ := Coeff.phaseFlow (fun n => c*n) t
  invFun := Coeff.phaseFlow (fun n => c*n) (-t)
  left_inv a := by simp [Coeff.phaseFlow_add]
  right_inv a := by simp [Coeff.phaseFlow_add]

@[simp] theorem Coeff.spatialTranslation_apply (c t : ℝ) (a : Coeff p) (n : ℤ) :
    spatialTranslation c t a n = Complex.exp ((t*(c*n) : ℝ)*Complex.I)*a n := rfl

@[simp] theorem Coeff.spatialTranslation_zero (c : ℝ) (a : Coeff p) :
    spatialTranslation c 0 a = a := phaseFlow_zero _ a

theorem Coeff.spatialTranslation_add (c t s : ℝ) (a : Coeff p) :
    spatialTranslation c t (spatialTranslation c s a) = spatialTranslation c (t+s) a :=
  phaseFlow_add _ _ _ _

/-- Translation is jointly continuous at every finite exponent. -/
theorem Coeff.continuous_spatialTranslation (hp : p ≠ ⊤) (c : ℝ) :
    Continuous (fun x : ℝ × Coeff p => spatialTranslation c x.1 x.2) :=
  continuous_phaseFlow hp _

/-- The same translation on any weighted coefficient space. -/
def WeightedCoeff.spatialTranslation (w : Weight) (c t : ℝ) :
    WeightedCoeff w p ≃ₗᵢ[ℂ] WeightedCoeff w p where
  __ := WeightedCoeff.phaseFlow w (fun n => c*n) t
  invFun := WeightedCoeff.phaseFlow w (fun n => c*n) (-t)
  left_inv a := by simp [WeightedCoeff.phaseFlow_add]
  right_inv a := by simp [WeightedCoeff.phaseFlow_add]

@[simp] theorem WeightedCoeff.spatialTranslation_apply (w : Weight) (c t : ℝ)
    (a : WeightedCoeff w p) (n : ℤ) :
    (spatialTranslation w c t a).val n = Complex.exp ((t*(c*n) : ℝ)*Complex.I)*a.val n :=
  phaseFlow_apply _ _ _ _ _

/-- The phase character turns sums of integer frequencies into products. -/
theorem spatialTranslation_phase_add (c t : ℝ) (n k : ℤ) :
    Complex.exp ((t*(c*((n+k : ℤ) : ℝ)) : ℝ)*Complex.I) =
      Complex.exp ((t*(c*n) : ℝ)*Complex.I) *
        Complex.exp ((t*(c*k) : ℝ)*Complex.I) := by
  rw [Int.cast_add, mul_add, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- Doubling the Fourier indices halves the frequency scale of translation. -/
theorem Coeff.periodDouble_spatialTranslation (c t : ℝ) (a : Coeff p) :
    periodDouble (spatialTranslation (2*c) t a) = spatialTranslation c t (periodDouble a) := by
  ext n
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he, periodDouble_even, spatialTranslation_apply, spatialTranslation_apply,
      periodDouble_even]
    congr 3
    push_cast
    ring
  · have he : n = 2*(n/2)+1 := by omega
    rw [he, periodDouble_odd, spatialTranslation_apply, periodDouble_odd, mul_zero]

end NLS
