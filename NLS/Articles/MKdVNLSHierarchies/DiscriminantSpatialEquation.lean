import NLS.ZakharovShabat.L2WholeLineDiscriminantXiIntegral

/-! # Division-free physical core of Theorem 6(v), on the original L2 domain

The gradient agrees with the actual physical Fréchet gradient on one period
and has its actual whole-line fundamental-matrix continuation. Its equation
holds almost everywhere for rough sources; its scalar coefficient is period
one and has a normalized integral at every positive and negative real point.
The R-integral sign below follows the stated physical ODE convention.
Source-convention comparison and the remaining xi symmetries are separate.
-/
noncomputable section
open Set Complex MeasureTheory NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

theorem theorem6_v_physical_gradient_agreement (u : IntervalPairL2) (z : ℂ)
    (x : Icc (0:ℝ) 1) :
    l2WholeLineDiscriminantGradient u z x = l2DiscriminantGradient u z x :=
  l2WholeLineDiscriminantGradient_on_unit u z x

theorem theorem6_v_physical_periodicity (u : IntervalPairL2) (z : ℂ) :
    Function.Periodic (l2WholeLineDiscriminantGradient u z) 1 ∧
      Function.Periodic (l2WholeLineDiscriminantXi u z) 1 :=
  ⟨periodic_l2WholeLineDiscriminantGradient u z,periodic_l2WholeLineDiscriminantXi u z⟩

theorem theorem6_v_physical_spatial_equation (u : IntervalPairL2) (z : ℂ) :
    ∀ᵐ x : ℝ, HasDerivAt (l2WholeLineDiscriminantGradient u z)
      (2*I*z*(l2WholeLineDiscriminantGradient u z x).1+
        l2WholeLineDiscriminantXi u z x*(l2WholeLinePotential u x).2,
       -2*I*z*(l2WholeLineDiscriminantGradient u z x).2-
        l2WholeLineDiscriminantXi u z x*(l2WholeLinePotential u x).1) x :=
  ae_hasDerivAt_l2WholeLineDiscriminantGradient u z

theorem theorem6_v_physical_scalar_integral (u : IntervalPairL2) (z : ℂ) (t : ℝ) :
    l2WholeLineDiscriminantXi u z t = (l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1-
      2*I*∫ x in (0:ℝ)..t,
        (I*(l2WholeLinePotential u x).1)*(l2WholeLineDiscriminantGradient u z x).1+
        (-I*(l2WholeLinePotential u x).2)*(l2WholeLineDiscriminantGradient u z x).2 :=
  l2WholeLineDiscriminantXi_eq_R_integral u z t

end NLS.Articles.MKdVNLSHierarchies
