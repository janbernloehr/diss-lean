import NLS.ZakharovShabat.L2NormalizedNonlocalGradient

/-! # The local spatial residual of the normalized actual gradient -/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.ZakharovShabat

def l2NormalizedLocalResidual (u : IntervalPairL2) (z r : ℂ) (x : ℝ) : ℂ × ℂ :=
  ((deriv (l2NormalizedDiscriminantGradient u z r) x).1-
      2*I*z*(l2NormalizedDiscriminantGradient u z r x).1,
   (deriv (l2NormalizedDiscriminantGradient u z r) x).2+
      2*I*z*(l2NormalizedDiscriminantGradient u z r x).2)

theorem ae_l2NormalizedLocalResidual_eq_xi (u : IntervalPairL2) (z r : ℂ) :
    ∀ᵐ x : ℝ, l2NormalizedLocalResidual u z r x =
      (l2WholeLineDiscriminantXi u z x/r*(l2WholeLinePotential u x).2,
       -(l2WholeLineDiscriminantXi u z x/r)*(l2WholeLinePotential u x).1) := by
  filter_upwards [ae_hasDerivAt_l2NormalizedDiscriminantGradient u z r] with x hx
  unfold l2NormalizedLocalResidual
  rw [hx.deriv]
  have hi := l2DiscriminantXi_div_eq_normalized_integral u z r x
  apply Prod.ext <;> dsimp
  · linear_combination -(l2WholeLinePotential u x).2*hi
  · linear_combination (l2WholeLinePotential u x).1*hi

end NLS.ZakharovShabat
