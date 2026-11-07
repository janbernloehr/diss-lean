import NLS.KdV.PeriodOneHamiltonian
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Exact first and second physical energy variations along real analytic
H1 curves through zero. The nonlinear inverse acceleration contributes
nothing to the second variation, since the physical energy is stationary there. -/
noncomputable section
open Complex NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

theorem fderiv_periodOneKdVHamiltonian_apply (q h : ScalarDomain 2) :
    (fderiv ℂ periodOneKdVHamiltonian q) h=periodOneSobolevKinetic (q,h)+
      periodOneCircleMean (3*(periodOneSobolevSynthesis q)^2*periodOneSobolevSynthesis h) := by
  have hline : HasDerivAt (fun z : ℂ => q+z • h) h 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0:ℂ)).smul_const h).const_add q
  have hd := (analyticAt_periodOneKdVHamiltonian q).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq
    (0:ℂ) hline (by simp)
  exact hd.unique (hasDerivAt_periodOneKdVHamiltonian q h)

theorem hasDerivAt_periodOneKdV_real_curve (q : ℝ → ScalarDomain 2) (t : ℝ)
    (hq : DifferentiableAt ℝ q t) :
    HasDerivAt (fun s : ℝ => (periodOneKdVHamiltonian (q s)).re)
      (periodOneSobolevKinetic (q t,deriv q t)+
        periodOneCircleMean (3*(periodOneSobolevSynthesis (q t))^2*
          periodOneSobolevSynthesis (deriv q t))).re t := by
  have hd := ((analyticAt_periodOneKdVHamiltonian (q t)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hq.hasDerivAt
  change HasDerivAt (fun s : ℝ => periodOneKdVHamiltonian (q s))
    ((fderiv ℂ periodOneKdVHamiltonian (q t)) (deriv q t)) t at hd
  rw [fderiv_periodOneKdVHamiltonian_apply] at hd
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd

theorem hasDerivAt_periodOneKdV_real_curve_variation_zero
    (q : ℝ → ScalarDomain 2) (hq : AnalyticAt ℝ q 0) (h0 : q 0=0) :
    HasDerivAt (fun t : ℝ => (periodOneSobolevKinetic (q t,deriv q t)+
      periodOneCircleMean (3*(periodOneSobolevSynthesis (q t))^2*
        periodOneSobolevSynthesis (deriv q t))).re)
      (periodOneSobolevKinetic (deriv q 0,deriv q 0)).re 0 := by
  let Bc : ScalarDomain 2 →L[ℂ] ScalarDomain 2 →L[ℂ] ℂ :=
    Coeff.dualPairing.bilinearComp
      (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp periodOneDerivative) periodOneDerivative
  let B := Bc.bilinearRestrictScalars ℝ
  have heB (a b : ScalarDomain 2) : B a b=periodOneSobolevKinetic (a,b) := rfl
  have hq0 := hq.differentiableAt.hasDerivAt
  have hdq := hq.deriv.differentiableAt.hasDerivAt
  have hkRaw := B.hasDerivAt_of_bilinear (fun _ => hq0) (fun _ => hdq)
  have hk : HasDerivAt (fun t : ℝ => periodOneSobolevKinetic (q t,deriv q t))
      (periodOneSobolevKinetic (deriv q 0,deriv q 0)) 0 := by
    simpa only [h0,map_zero,zero_apply,zero_add,heB] using hkRaw
  have hS := (periodOneSobolevSynthesis.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hq0
  have hDS := (periodOneSobolevSynthesis.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hdq
  change HasDerivAt (fun t : ℝ => periodOneSobolevSynthesis (q t))
    (periodOneSobolevSynthesis (deriv q 0)) 0 at hS
  change HasDerivAt (fun t : ℝ => periodOneSobolevSynthesis (deriv q t))
    (periodOneSobolevSynthesis (deriv (deriv q) 0)) 0 at hDS
  have hCub := ((hS.pow 2).const_mul 3).mul hDS
  have hCub0 : HasDerivAt (fun t : ℝ =>
      3*(periodOneSobolevSynthesis (q t))^2*periodOneSobolevSynthesis (deriv q t)) 0 0 := by
    simpa [h0] using! hCub
  have hMean := (periodOneCircleMean.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hCub0
  change HasDerivAt (fun t : ℝ => periodOneCircleMean
    (3*(periodOneSobolevSynthesis (q t))^2*periodOneSobolevSynthesis (deriv q t))) (periodOneCircleMean 0) 0 at hMean
  rw [map_zero] at hMean
  have hsum := hk.add hMean
  simp only [add_zero] at hsum
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hsum

end NLS.KdV
