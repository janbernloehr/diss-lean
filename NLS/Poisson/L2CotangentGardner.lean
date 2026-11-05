import NLS.Poisson.L2GardnerSkew

/-! # Gardner skew symmetry for actual bounded cotangents

This applies to branch-independent angular differentials as well as to
Frechet derivatives of globally defined scalar functions.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson

def l2CotangentGradient (L : Coeff 2 →L[ℂ] ℂ) : Coeff 2 :=
  Coeff.reflection (Coeff.hilbertCotangentCoefficients L)

@[simp] theorem l2CotangentGradient_apply (L : Coeff 2 →L[ℂ] ℂ) (n : ℤ) :
    l2CotangentGradient L n = L (lp.single 2 (-n) 1) := by
  rw [l2CotangentGradient,Coeff.reflection_apply,Coeff.hilbertCotangentCoefficients_apply]

theorem l2CotangentGradient_represents (L : Coeff 2 →L[ℂ] ℂ) (h : Coeff 2) :
    Coeff.dualPairing (Coeff.reflection (l2CotangentGradient L)) h = L h := by
  rw [l2CotangentGradient,Coeff.reflection_reflection,Coeff.dualPairing_hilbertCotangentCoefficients]

theorem l2CotangentGardner_skew (L M : Coeff 2 →L[ℂ] ℂ)
    (hL : Memℓp (fun n : ℤ => 2*I*(Real.pi : ℂ)*n*l2CotangentGradient L n) 2)
    (hM : Memℓp (fun n : ℤ => 2*I*(Real.pi : ℂ)*n*l2CotangentGradient M n) 2) :
    L (l2SpatialDerivative (l2CotangentGradient M)) =
      -M (l2SpatialDerivative (l2CotangentGradient L)) := by
  rw [← l2CotangentGradient_represents L,← l2CotangentGradient_represents M]
  exact dualPairing_spatialDerivative_skew _ _ hL hM

end NLS.Poisson
