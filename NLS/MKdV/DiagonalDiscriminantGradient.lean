import NLS.ZakharovShabat.ClassicalDiscriminantCommutation
import NLS.Fourier.UnitIntervalDerivativeCoefficient

/-! # The physical diagonal gradient identity underlying Gardner transfer

The actual trace gradient satisfies a closed first-order system. On a
coefficient diagonal its sum has derivative 2*i*z times its difference.
Its matching endpoints give the exact original period-one Fourier identity.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat
namespace NLS.MKdV

theorem hasDerivAt_diagonalDiscriminantGradient_sum (Φ : Curve (ℂ × ℂ))
    (hΦ : ∀ t, (Φ t).1 = (Φ t).2) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (fun s => (classicalDiscriminantGradient Φ z s).1+(classicalDiscriminantGradient Φ z s).2)
      (2*I*z*((classicalDiscriminantGradient Φ z t).1-(classicalDiscriminantGradient Φ z t).2)) t := by
  convert! (hasDerivAt_classicalDiscriminantGradient_fst Φ z t).add
    (hasDerivAt_classicalDiscriminantGradient_snd Φ z t) using 1
  rw [hΦ t]
  ring

theorem diagonalDiscriminantGradient_fourier (Φ : Curve (ℂ × ℂ))
    (hΦ : ∀ t, (Φ t).1 = (Φ t).2) (z : ℂ) (n : ℤ) :
    (2*I*(Real.pi : ℂ)*n) *
        unitFourierCoefficient (fun s => (classicalDiscriminantGradient Φ z s).1+
          (classicalDiscriminantGradient Φ z s).2) n =
      2*I*z*unitFourierCoefficient (fun s => (classicalDiscriminantGradient Φ z s).1-
        (classicalDiscriminantGradient Φ z s).2) n := by
  have hc := continuous_classicalDiscriminantGradient Φ z
  have hd := unitFourierCoefficient_of_hasDerivAt
    (fun s => (classicalDiscriminantGradient Φ z s).1+(classicalDiscriminantGradient Φ z s).2)
    (fun s => 2*I*z*((classicalDiscriminantGradient Φ z s).1-(classicalDiscriminantGradient Φ z s).2))
    (hc.fst.add hc.snd) (continuous_const.mul (hc.fst.sub hc.snd))
    (fun s hs => hasDerivAt_diagonalDiscriminantGradient_sum Φ hΦ z ⟨s,hs⟩)
    (by rw [classicalDiscriminantGradient_one,classicalDiscriminantGradient_zero]) n
  have he : unitFourierCoefficient
      (fun s => 2*I*z*((classicalDiscriminantGradient Φ z s).1-(classicalDiscriminantGradient Φ z s).2)) n =
      2*I*z*unitFourierCoefficient (fun s => (classicalDiscriminantGradient Φ z s).1-
        (classicalDiscriminantGradient Φ z s).2) n := by
    unfold unitFourierCoefficient
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  exact hd.symm.trans he

end NLS.MKdV
