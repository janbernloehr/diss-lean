import NLS.Poisson.L2Gardner

/-! # Skew symmetry on the actual L2 Gardner domain

The Fourier integration-by-parts identity uses the original period-one
symbol. Both spatial derivatives must belong to L2; no fallback value
is used to assert skew symmetry outside this domain.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson

theorem dualPairing_spatialDerivative_skew (g h : Coeff 2)
    (hg : Memℓp (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*g m) 2)
    (hh : Memℓp (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*h m) 2) :
    Coeff.dualPairing (Coeff.reflection g) (l2SpatialDerivative h) =
      -Coeff.dualPairing (Coeff.reflection h) (l2SpatialDerivative g) := by
  rw [Coeff.dualPairing_apply,Coeff.dualPairing_apply,
    ← (Equiv.neg ℤ).tsum_eq (fun m : ℤ => Coeff.reflection h m*l2SpatialDerivative g m),← tsum_neg]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply,Coeff.reflection_apply,l2SpatialDerivative_apply g hg,
    l2SpatialDerivative_apply h hh,Int.cast_neg,neg_neg]
  ring

theorem l2GardnerBracket_antisymm_of_memlp (F G : Coeff 2 → ℂ) (a : Coeff 2)
    (hF : Memℓp (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*l2ScalarGradient F a m) 2)
    (hG : Memℓp (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*l2ScalarGradient G a m) 2) :
    l2GardnerBracket F G a = -l2GardnerBracket G F a := by
  calc
    _ = Coeff.dualPairing (Coeff.reflection (l2ScalarGradient F a))
        (l2SpatialDerivative (l2ScalarGradient G a)) :=
      (l2ScalarGradient_represents F a _).symm
    _ = -Coeff.dualPairing (Coeff.reflection (l2ScalarGradient G a))
        (l2SpatialDerivative (l2ScalarGradient F a)) :=
      dualPairing_spatialDerivative_skew _ _ hF hG
    _ = _ := congrArg Neg.neg (l2ScalarGradient_represents G a _)

theorem l2GardnerBracket_self_eq_zero_of_memlp (F : Coeff 2 → ℂ) (a : Coeff 2)
    (hF : Memℓp (fun m : ℤ => 2*I*(Real.pi : ℂ)*m*l2ScalarGradient F a m) 2) :
    l2GardnerBracket F F a = 0 := by
  have h := l2GardnerBracket_antisymm_of_memlp F F a hF hF
  linear_combination (1/2 : ℂ)*h

end NLS.Poisson
