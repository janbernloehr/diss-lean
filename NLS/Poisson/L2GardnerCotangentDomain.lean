import NLS.Poisson.L2Gardner
import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian

/-! # The actual Gardner domain from a bounded cotangent extension

If applying a cotangent to the period-one derivative extends boundedly
to L2, its reflected bilinear gradient has an L2 spatial derivative.
The Fourier coefficients identify that derivative without a fallback.
-/
noncomputable section
open Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Poisson

theorem periodOneDerivative_scalarMode (k : ℤ) :
    periodOneDerivative (scalarMode k 1) =
      (2*I*(Real.pi : ℂ)*k) • (lp.single 2 k 1 : Coeff 2) := by
  ext j
  simp only [periodOneDerivative_apply,scalarMode_apply,lp.coeFn_smul,Pi.smul_apply,
    smul_eq_mul,lp.single_apply,Pi.single_apply]
  split_ifs with hj
  · subst j
    ring
  · simp

theorem spatialGradient_coefficient_of_cotangent_extension
    (A L : Coeff 2 →L[ℂ] ℂ)
    (hAL : A.comp periodOneDerivative = L.comp scalarInclusion) (m : ℤ) :
    2*I*(Real.pi : ℂ)*m*A (lp.single 2 (-m) 1) = -L (lp.single 2 (-m) 1) := by
  have h := congrArg (fun T : ScalarDomain 2 →L[ℂ] ℂ => T (scalarMode (-m) 1)) hAL
  change A (periodOneDerivative (scalarMode (-m) 1)) = L (scalarInclusion (scalarMode (-m) 1)) at h
  rw [periodOneDerivative_scalarMode,scalarInclusion_scalarMode,map_smul,smul_eq_mul,Int.cast_neg] at h
  linear_combination -h

theorem memlp_spatialGradient_of_cotangent_extension
    (A L : Coeff 2 →L[ℂ] ℂ)
    (hAL : A.comp periodOneDerivative = L.comp scalarInclusion) :
    Memℓp (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*A (lp.single 2 (-m) 1)) 2 := by
  have he : (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*A (lp.single 2 (-m) 1)) =
      (fun m => (-Coeff.reflection (Coeff.hilbertCotangentCoefficients L)) m) := by
    funext m
    simp only [lp.coeFn_neg,Pi.neg_apply,Coeff.reflection_apply,Coeff.hilbertCotangentCoefficients_apply]
    exact spatialGradient_coefficient_of_cotangent_extension A L hAL m
  rw [he]
  exact lp.memℓp (-Coeff.reflection (Coeff.hilbertCotangentCoefficients L))

theorem l2GardnerDirection_eq_of_cotangent_extension
    (F : Coeff 2 → ℂ) (a : Coeff 2) (L : Coeff 2 →L[ℂ] ℂ)
    (hAL : (fderiv ℂ F a).comp periodOneDerivative = L.comp scalarInclusion) :
    l2GardnerDirection F a = -Coeff.reflection (Coeff.hilbertCotangentCoefficients L) := by
  have hm : Memℓp (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*l2ScalarGradient F a m) 2 := by
    simp only [l2ScalarGradient_apply]
    exact memlp_spatialGradient_of_cotangent_extension _ L hAL
  ext m
  rw [l2GardnerDirection,l2SpatialDerivative_apply _ hm,l2ScalarGradient_apply]
  simp only [lp.coeFn_neg,Pi.neg_apply,Coeff.reflection_apply,Coeff.hilbertCotangentCoefficients_apply]
  exact spatialGradient_coefficient_of_cotangent_extension _ L hAL m

theorem l2GardnerDirection_distribution_of_cotangent_extension
    (F : Coeff 2 → ℂ) (a : Coeff 2) (L : Coeff 2 →L[ℂ] ℂ)
    (hAL : (fderiv ℂ F a).comp periodOneDerivative = L.comp scalarInclusion) :
    TemperedDistribution.derivCLM ℂ (NLS.Fourier.periodOneL2Distribution (l2ScalarGradient F a)) =
      NLS.Fourier.periodOneL2Distribution (l2GardnerDirection F a) := by
  apply l2SpatialDerivative_distribution
  simp only [l2ScalarGradient_apply]
  exact memlp_spatialGradient_of_cotangent_extension _ L hAL

end NLS.Poisson
