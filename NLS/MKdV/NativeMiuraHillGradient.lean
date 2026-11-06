import NLS.MKdV.NativeMiuraHillHamiltonian
import NLS.MKdV.SobolevMiuraHillFlowRestriction

/-! # Actual gradients on the native scalar hierarchy domain -/
noncomputable section
open NLS.ZakharovShabat NLS.Fourier
open scoped ContDiff SchwartzMap
namespace NLS.MKdV

def nativeMiuraHillGradient (s : ℕ) (u : ScalarSobolev s) : NegativeScalarSobolev s :=
  WeightedCoeff.sobolevCotangentCLM (p := 2) (q := 2) (s : ℝ) (by norm_num)
    (fderiv ℂ (nativeMiuraHillHamiltonian s) u)

theorem analyticAt_nativeMiuraHillGradient (s : ℕ) (u : ScalarSobolev s) :
    AnalyticAt ℂ (nativeMiuraHillGradient s) u :=
  ((WeightedCoeff.sobolevCotangentCLM (p := 2) (q := 2) (s : ℝ) (by norm_num)).analyticAt _).comp
    (analyticAt_nativeMiuraHillHamiltonian s u).fderiv

theorem nativeMiuraHillGradient_represents (s : ℕ) (u h : ScalarSobolev s) :
    WeightedCoeff.sobolevBilinearPairing (s : ℝ) h (nativeMiuraHillGradient s u) =
      fderiv ℂ (nativeMiuraHillHamiltonian s) u h := by
  rw [nativeMiuraHillGradient,WeightedCoeff.sobolevCotangentCLM_apply,
    WeightedCoeff.sobolevBilinearPairing_sobolevCotangent]

theorem nativeMiuraHillGradient_eq_classical (s : ℕ) (u : ScalarSobolev s) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ j, u.val j = periodOneCoefficient f j) (n : ℤ) :
    (nativeMiuraHillGradient s u).val n = periodOneCoefficient (classicalMiuraHillGradient f (s+1)) n := by
  apply scalarCotangent_eq_classical
  intro h g hg hpg hgc
  exact fderiv_scalarSobolev_eq_smooth_variation s _ (fun v => classicalMiuraHillHamiltonian v (s+1))
    u h f g (analyticAt_nativeMiuraHillHamiltonian s u)
    (fun a v hv hpv hvc => nativeMiuraHillHamiltonian_eq_classical s a v hv hpv hvc)
    hf hg hp hpg hc hgc _ (hasDerivAt_classicalMiuraHillHamiltonian f g hf hg hp hpg (s+1))

/-- Native and higher-regularity gradients represent the same actual physical
distribution, despite being constructed in different opposite Sobolev norms. -/
theorem nativeMiuraHillGradient_eq_previous (s : ℕ) (u : ScalarSobolev (s+1)) (n : ℤ) :
    (nativeMiuraHillGradient s (hierarchySobolevInclusion (s+1) s (by omega) u)).val n =
      (sobolevMiuraHillGradient (s+1) (by omega) u).val n := by
  let EN : NegativeScalarSobolev s →L[ℂ] ℂ := WeightedCoeff.evalCLM _ 2 n
  let EO : NegativeScalarSobolev (s+1) →L[ℂ] ℂ := WeightedCoeff.evalCLM _ 2 n
  have hN : Continuous (nativeMiuraHillGradient s) :=
    continuous_iff_continuousAt.mpr (fun v => (analyticAt_nativeMiuraHillGradient s v).continuousAt)
  have hO : Continuous (sobolevMiuraHillGradient (s+1) (by omega)) :=
    continuous_iff_continuousAt.mpr (fun v =>
      (analyticAt_sobolevMiuraHillGradient (s+1) (by omega) v).continuousAt)
  have he := eq_of_continuous_of_smooth_scalarSobolev (s+1)
    (fun v => (nativeMiuraHillGradient s (hierarchySobolevInclusion (s+1) s (by omega) v)).val n)
    (fun v => (sobolevMiuraHillGradient (s+1) (by omega) v).val n)
    ((EN.continuous.comp hN).comp (hierarchySobolevInclusion (s+1) s (by omega)).continuous)
    (EO.continuous.comp hO) (by
      intro v f hf hp hc
      rw [nativeMiuraHillGradient_eq_classical s _ f hf hp
        (fun j => by simpa only [hierarchySobolevInclusion_apply] using hc j),
        sobolevMiuraHillGradient_eq_classical (s+1) (by omega) v f hf hp hc])
  exact congrFun he u

def nativeMiuraHillVectorField (s : ℕ) (u : ScalarSobolev s) : 𝓢'(ℝ,ℂ) :=
  TemperedDistribution.derivCLM ℂ (periodOneSobolevDistribution (-(s : ℝ)) (nativeMiuraHillGradient s u))

theorem nativeMiuraHillVectorField_eq_previous (s : ℕ) (u : ScalarSobolev (s+1)) :
    nativeMiuraHillVectorField s (hierarchySobolevInclusion (s+1) s (by omega) u) =
      sobolevMiuraHillVectorField (s+1) (by omega) u := by
  apply congrArg (TemperedDistribution.derivCLM ℂ)
  apply periodicDistribution_ext_arbitraryPeriod 1 (by norm_num)
    (periodOneSobolevDistribution_periodic _ _) (periodOneSobolevDistribution_periodic _ _)
  intro n
  rw [periodOneSobolevDistribution_coefficient,periodOneSobolevDistribution_coefficient]
  exact nativeMiuraHillGradient_eq_previous s u n

/-- On the original complex H^(s+1) inputs, the actual derivative of the
native H^s gradient is represented by each even NLS vector-field component. -/
theorem nativeMiuraHillFlowRestriction (s : ℕ) (u : ScalarSobolev (s+1)) :
    (periodOneSobolevDistribution (-((s+1 : ℕ) : ℝ))
        (sobolevEvenHierarchyVectorField (s+1) (by omega) (u,u)).1,
      periodOneSobolevDistribution (-((s+1 : ℕ) : ℝ))
        (sobolevEvenHierarchyVectorField (s+1) (by omega) (u,u)).2) =
      (nativeMiuraHillVectorField s (hierarchySobolevInclusion (s+1) s (by omega) u),
        nativeMiuraHillVectorField s (hierarchySobolevInclusion (s+1) s (by omega) u)) := by
  rw [nativeMiuraHillVectorField_eq_previous]
  exact sobolevMiuraHillFlowRestriction (s+1) (by omega) u

end NLS.MKdV
