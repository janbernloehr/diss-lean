import NLS.MKdV.HillNativeMagriIntegral
import NLS.KdV.HillNativeCotangents
import NLS.KdV.HillPhysicalFourierCoefficients
import NLS.KdV.HillLogNormingMagriBrackets

/-! # Independent spectral Magri geometry in the native coefficient spaces

These are the original interval gradients lifted by their literal Fourier
coefficients. Their full bracket matrix holds for every real period-one
L² Hill potential, including all closed gaps.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.Fourier NLS.Poisson NLS.ZakharovShabat NLS.KdV
namespace NLS.MKdV

theorem hillSobolevMagriBivector_eq_weakGradientMagri
    (q : RealPeriodOneHillPotential) (D E : PeriodOneH2CurveData) :
    hillSobolevMagriBivector (Coeff.periodHalve (SpectralWeight.one.toCoeff q.val)) D.native E.native =
      hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val)
        D.profile D.spatial D.second E.profile E.spatial :=
  hillSobolevMagriBivector_eq_curve_integral _ _ (memLp_hillIntervalPotential _)
    (fun n => (periodOneCoefficient_hillIntervalPotential _ q.property.1 n).symm) D E

theorem hillNativeDirichlet_Magri_bracket (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    hillSobolevMagriBivector (Coeff.periodHalve (SpectralWeight.one.toCoeff q.val))
      (hillDirichletNativeGradient q n hn) (hillDirichletNativeGradient q m hm) = 0 := by
  rw [hillDirichletNativeGradient,hillDirichletNativeGradient,
    hillSobolevMagriBivector_eq_weakGradientMagri]
  exact hillDirichletMagriBracket_eq_zero q n m hn hm

theorem hillNativeDirichlet_logNorming_Magri_bracket (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    hillSobolevMagriBivector (Coeff.periodHalve (SpectralWeight.one.toCoeff q.val))
      (hillDirichletNativeGradient q n hn) (hillLogNormingNativeGradient q m hm) =
        if n = m then -2*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) else 0 := by
  rw [hillDirichletNativeGradient,hillLogNormingNativeGradient,
    hillSobolevMagriBivector_eq_weakGradientMagri]
  exact hillDirichletLogMagriBracket_eq q n m hn hm

theorem hillNativeLogNorming_dirichlet_Magri_bracket (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    hillSobolevMagriBivector (Coeff.periodHalve (SpectralWeight.one.toCoeff q.val))
      (hillLogNormingNativeGradient q n hn) (hillDirichletNativeGradient q m hm) =
        if n = m then 2*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) else 0 := by
  rw [hillLogNormingNativeGradient,hillDirichletNativeGradient,
    hillSobolevMagriBivector_eq_weakGradientMagri]
  exact hillLogDirichletMagriBracket_eq q n m hn hm

theorem hillNativeLogNorming_Magri_bracket (q : RealPeriodOneHillPotential) (n m : ℕ)
    (hn : 1 ≤ n) (hm : 1 ≤ m) :
    hillSobolevMagriBivector (Coeff.periodHalve (SpectralWeight.one.toCoeff q.val))
      (hillLogNormingNativeGradient q n hn) (hillLogNormingNativeGradient q m hm) = 0 := by
  rw [hillLogNormingNativeGradient,hillLogNormingNativeGradient,
    hillSobolevMagriBivector_eq_weakGradientMagri]
  exact hillLogNormingMagriBracket_eq_zero q n m hn hm

end NLS.MKdV
