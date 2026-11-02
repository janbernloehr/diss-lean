import NLS.Poisson.SourceBivector
import NLS.Fourier.PeriodOneDistributionDerivative

/-! # The literal period-one L2 Gardner direction

The physical bilinear gradient is constructed from the actual Frechet
derivative. Spatial differentiation uses its original 2*pi*i*m Fourier
multiplier; whenever square summability holds, it is the actual tempered
distribution derivative. No hierarchy or NLS action defines this operator.
-/
noncomputable section
open Complex NLS.Fourier
open scoped ENNReal SchwartzMap Classical
namespace NLS.Poisson

def l2ScalarGradient (F : Coeff 2 → ℂ) (a : Coeff 2) : Coeff 2 :=
  Coeff.reflection (Coeff.hilbertCotangentCoefficients (fderiv ℂ F a))

@[simp] theorem l2ScalarGradient_apply (F : Coeff 2 → ℂ) (a : Coeff 2) (m : ℤ) :
    l2ScalarGradient F a m = fderiv ℂ F a (lp.single 2 (-m) 1) := by
  rw [l2ScalarGradient,Coeff.reflection_apply,Coeff.hilbertCotangentCoefficients_apply]

theorem l2ScalarGradient_represents (F : Coeff 2 → ℂ) (a h : Coeff 2) :
    Coeff.dualPairing (Coeff.reflection (l2ScalarGradient F a)) h = fderiv ℂ F a h := by
  rw [l2ScalarGradient,Coeff.reflection_reflection,Coeff.dualPairing_hilbertCotangentCoefficients]

def l2SpatialDerivative (a : Coeff 2) : Coeff 2 :=
  if h : Memℓp (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*a m) 2 then ⟨_,h⟩ else 0

theorem l2SpatialDerivative_apply (a : Coeff 2)
    (ha : Memℓp (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*a m) 2) (m : ℤ) :
    l2SpatialDerivative a m = 2*I*(Real.pi : ℂ)*m*a m := by
  rw [l2SpatialDerivative,dif_pos ha]

theorem l2SpatialDerivative_distribution (a : Coeff 2)
    (ha : Memℓp (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*a m) 2) :
    TemperedDistribution.derivCLM ℂ (periodOneL2Distribution a) =
      periodOneL2Distribution (l2SpatialDerivative a) :=
  periodOneL2Distribution_derivative_eq a _ (l2SpatialDerivative_apply a ha)

def l2GardnerDirection (F : Coeff 2 → ℂ) (a : Coeff 2) : Coeff 2 :=
  l2SpatialDerivative (l2ScalarGradient F a)

def l2GardnerBracket (F G : Coeff 2 → ℂ) (a : Coeff 2) : ℂ :=
  fderiv ℂ F a (l2GardnerDirection G a)

end NLS.Poisson
