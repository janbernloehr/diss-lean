import NLS.ZakharovShabat.SobolevTopJetPhysical
import NLS.Fourier.PeriodOneCircleMean
import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.Reflection

/-! # The actual KdV and KdV2 Hamiltonians on their full native domains

These are bounded complex polynomial expressions in the ORIGINAL Fourier
jets and continuous physical representatives. The domains are exactly H1
and H2. No action, spectral formula, or smoothness premise defines them.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

/-- The bilinear physical square of the highest actual Fourier derivative. -/
def nativeTopJetSquare (s : ℕ) (a : ScalarSobolev s) : ℂ :=
  Coeff.dualPairing (Coeff.reflection (hierarchySobolevJetL2 s s le_rfl a))
    (hierarchySobolevJetL2 s s le_rfl a)

/-- Article H1, on the FULL original H1 source domain: half the derivative
square plus the cubic physical mean. -/
def nativeKdVHamiltonian (a : ScalarSobolev 1) : ℂ :=
  (1/2 : ℂ)*nativeTopJetSquare 1 a+
    periodOneCircleMean ((hierarchySobolevJetContinuous 1 0 (by omega) a)^3)

/-- Article H2, on the FULL original H2 source domain, with the exact
coefficients 1/2, 5 and 5/2 in the original unit-period convention. -/
def nativeKdV2Hamiltonian (a : ScalarSobolev 2) : ℂ :=
  (1/2 : ℂ)*nativeTopJetSquare 2 a+
    5*periodOneCircleMean ((hierarchySobolevJetContinuous 2 0 (by omega) a)*
      (hierarchySobolevJetContinuous 2 1 (by omega) a)^2)+
    (5/2 : ℂ)*periodOneCircleMean ((hierarchySobolevJetContinuous 2 0 (by omega) a)^4)

theorem analyticAt_nativeTopJetSquare (s : ℕ) (a : ScalarSobolev s) :
    AnalyticAt ℂ (nativeTopJetSquare s) a := by
  let L := hierarchySobolevJetL2 s s le_rfl
  let R := Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp L
  exact (Coeff.dualPairing.analyticAt_bilinear (R a,L a)).comp
    (f := fun b => (R b,L b)) ((R.analyticAt a).prod (L.analyticAt a))

/-- The ORIGINAL physical KdV Hamiltonian is complex analytic on ALL H1. -/
theorem analyticAt_nativeKdVHamiltonian (a : ScalarSobolev 1) :
    AnalyticAt ℂ nativeKdVHamiltonian a := by
  exact (analyticAt_const.mul (analyticAt_nativeTopJetSquare 1 a)).add
    ((periodOneCircleMean.analyticAt _).comp
      (((hierarchySobolevJetContinuous 1 0 (by omega)).analyticAt a).pow 3))

/-- The ORIGINAL physical KdV2 Hamiltonian is complex analytic on ALL H2. -/
theorem analyticAt_nativeKdV2Hamiltonian (a : ScalarSobolev 2) :
    AnalyticAt ℂ nativeKdV2Hamiltonian a := by
  have h0 := (hierarchySobolevJetContinuous 2 0 (by omega)).analyticAt a
  have h1 := (hierarchySobolevJetContinuous 2 1 (by omega)).analyticAt a
  exact ((analyticAt_const.mul (analyticAt_nativeTopJetSquare 2 a)).add
    (analyticAt_const.mul ((periodOneCircleMean.analyticAt _).comp (h0.mul (h1.pow 2))))).add
      (analyticAt_const.mul ((periodOneCircleMean.analyticAt _).comp (h0.pow 4)))

/-- Bilinear Parseval identifies the top Fourier square with the ACTUAL
highest physical derivative at the full native Sobolev endpoint. -/
theorem nativeTopJetSquare_eq_integral (s : ℕ) (hs : 1≤s) (a : ScalarSobolev s) :
    nativeTopJetSquare s a=∫ x in (0 : ℝ)..1, (sobolevTopJetPhysical s hs a x)^2 := by
  have h := tsum_bilinear_unitFourierCoefficient_of_memLp
    (memLp_sobolevTopJetPhysical s hs a) (memLp_sobolevTopJetPhysical s hs a)
  have hc (f : ℝ → ℂ) (n : ℤ) : unitFourierCoefficient f n=periodOneCoefficient f n :=
    unitFourierCoefficient_eq_fourierCoeffOn f n
  simpa only [nativeTopJetSquare,Coeff.dualPairing_apply,Coeff.reflection_apply,hc,
    periodOneCoefficient_sobolevTopJetPhysical,pow_two] using h

end NLS.KdV
