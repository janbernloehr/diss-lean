import NLS.ZakharovShabat.L2WholeLineDiscriminantXiIntegral

/-! # The corrected typed nonlocal residual for normalized gradients

Normalization by a scalar independent of x commutes with the actual spatial
derivative and integral. The nonlocal scalar multiplies J*phi, and its sign
on the residual's left side is positive. No scalar is subtracted from a vector.
-/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.ZakharovShabat

def l2NormalizedDiscriminantGradient (u : IntervalPairL2) (z r : ℂ) (x : ℝ) : ℂ × ℂ :=
  r⁻¹ • l2WholeLineDiscriminantGradient u z x

def l2NormalizedDiscriminantRPairing (u : IntervalPairL2) (z r : ℂ) (x : ℝ) : ℂ :=
  (I*(l2WholeLinePotential u x).1)*(l2NormalizedDiscriminantGradient u z r x).1+
  (-I*(l2WholeLinePotential u x).2)*(l2NormalizedDiscriminantGradient u z r x).2

theorem l2DiscriminantXi_div_eq_normalized_integral (u : IntervalPairL2) (z r : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantXi u z x/r =
      ((l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1)/r-
        2*I*∫ t in (0:ℝ)..x, l2NormalizedDiscriminantRPairing u z r t := by
  have he : (fun t => l2NormalizedDiscriminantRPairing u z r t) =
      (fun t => r⁻¹*((I*(l2WholeLinePotential u t).1)*(l2WholeLineDiscriminantGradient u z t).1+
        (-I*(l2WholeLinePotential u t).2)*(l2WholeLineDiscriminantGradient u z t).2)) := by
    funext t
    simp only [l2NormalizedDiscriminantRPairing,l2NormalizedDiscriminantGradient,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    ring
  rw [he,intervalIntegral.integral_const_mul,l2WholeLineDiscriminantXi_eq_R_integral]
  simp only [div_eq_mul_inv]
  ring

theorem ae_hasDerivAt_l2NormalizedDiscriminantGradient (u : IntervalPairL2) (z r : ℂ) :
    ∀ᵐ x : ℝ, HasDerivAt (l2NormalizedDiscriminantGradient u z r)
      (2*I*z*(l2NormalizedDiscriminantGradient u z r x).1+
          (((l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1)/r-
            2*I*∫ t in (0:ℝ)..x, l2NormalizedDiscriminantRPairing u z r t)*(l2WholeLinePotential u x).2,
       -2*I*z*(l2NormalizedDiscriminantGradient u z r x).2-
          (((l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1)/r-
            2*I*∫ t in (0:ℝ)..x, l2NormalizedDiscriminantRPairing u z r t)*(l2WholeLinePotential u x).1) x := by
  filter_upwards [ae_hasDerivAt_l2WholeLineDiscriminantGradient u z] with x hx
  have h := hx.const_smul r⁻¹
  have hi := l2DiscriminantXi_div_eq_normalized_integral u z r x
  convert! h using 1
  apply Prod.ext <;>
    simp only [l2NormalizedDiscriminantGradient,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  · linear_combination -(l2WholeLinePotential u x).2*hi
  · linear_combination (l2WholeLinePotential u x).1*hi

def l2NormalizedNonlocalResidual (u : IntervalPairL2) (z r : ℂ) (x : ℝ) : ℂ × ℂ :=
  ((deriv (l2NormalizedDiscriminantGradient u z r) x).1-
      2*I*z*(l2NormalizedDiscriminantGradient u z r x).1+
      2*I*(∫ t in (0:ℝ)..x, l2NormalizedDiscriminantRPairing u z r t)*(l2WholeLinePotential u x).2,
   (deriv (l2NormalizedDiscriminantGradient u z r) x).2+
      2*I*z*(l2NormalizedDiscriminantGradient u z r x).2-
      2*I*(∫ t in (0:ℝ)..x, l2NormalizedDiscriminantRPairing u z r t)*(l2WholeLinePotential u x).1)

theorem ae_l2NormalizedNonlocalResidual_eq_boundary (u : IntervalPairL2) (z r : ℂ) :
    ∀ᵐ x : ℝ, l2NormalizedNonlocalResidual u z r x =
      (((l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1)/r*(l2WholeLinePotential u x).2,
       -((l2Monodromy u z) 0 0-(l2Monodromy u z) 1 1)/r*(l2WholeLinePotential u x).1) := by
  filter_upwards [ae_hasDerivAt_l2NormalizedDiscriminantGradient u z r] with x hx
  unfold l2NormalizedNonlocalResidual
  rw [hx.deriv]
  apply Prod.ext <;> dsimp <;> ring

end NLS.ZakharovShabat
