import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian
import NLS.ZakharovShabat.SourceFiniteGapSobolevHamiltonian

/-! # Physical momentum on the full period-one H¹ space

The convention is Appendix H's second Hamiltonian, `-i ∫ a b'`.
The definition uses bounded bilinear Fourier duality, independently of
spectral actions, and is analytic on the entire complex H¹ pair space.
-/
noncomputable section
open Set MeasureTheory Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
open NLS.Fourier

/-- Physical momentum, with the dissertation's sign and period-one normalization. -/
def periodOneSobolevMomentum (ab : ScalarDomain 2 × ScalarDomain 2) : ℂ :=
  -I * Coeff.dualPairing (Coeff.reflection (scalarInclusion ab.1)) (periodOneDerivative ab.2)

/-- The physical momentum is the unit-period integral of the actual H¹
representatives and their almost-everywhere classical derivative. -/
theorem periodOneSobolevMomentum_eq_integral (a b : ScalarDomain 2) :
    periodOneSobolevMomentum (a,b) = -I * ∫ x in (0 : ℝ)..1,
      periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ)) *
        deriv (fun t : ℝ => periodOneSobolevSynthesis b (t : AddCircle (2 : ℝ))) x := by
  have h := tsum_bilinear_unitFourierCoefficient_of_memLp
    (memLp_two_interval (continuous_periodOneSobolevSynthesis a) 0 1 (by norm_num))
    (memLp_deriv_periodOneSobolevSynthesis b)
  apply congrArg (fun z : ℂ => -I*z) at h
  have he (f : ℝ → ℂ) (n : ℤ) : unitFourierCoefficient f n = periodOneCoefficient f n :=
    unitFourierCoefficient_eq_fourierCoeffOn f n
  simpa only [he,
    periodOneCoefficient_periodOneSobolevSynthesis,periodOneCoefficient_deriv_periodOneSobolevSynthesis,
    periodOneSobolevMomentum,Coeff.dualPairing_apply,Coeff.reflection_apply,scalarInclusion_apply,
    periodOneDerivative_apply] using h

/-- The Fourier formula records the sign at both positive and negative modes. -/
theorem periodOneSobolevMomentum_eq_tsum (a b : ScalarDomain 2) :
    periodOneSobolevMomentum (a,b) = ∑' n : ℤ, (2*(Real.pi:ℂ)*n)*a.val (-n)*b.val n := by
  rw [periodOneSobolevMomentum,Coeff.dualPairing_apply,← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [Coeff.reflection_apply,scalarInclusion_apply,periodOneDerivative_apply]
  ring_nf
  simp only [I_sq]
  ring

/-- Opposite Fourier modes fix the exact sign and the `2π` normalization. -/
theorem periodOneSobolevMomentum_scalarModes (n : ℤ) (a b : ℂ) :
    periodOneSobolevMomentum (scalarMode (-n) a,scalarMode n b) = (2*(Real.pi:ℂ)*n)*a*b := by
  rw [periodOneSobolevMomentum_eq_tsum]
  simp [scalarMode_apply,mul_ite,ite_mul]

theorem analyticAt_periodOneSobolevMomentum (ab : ScalarDomain 2 × ScalarDomain 2) :
    AnalyticAt ℂ periodOneSobolevMomentum ab := by
  let A : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] Coeff 2 :=
    (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp scalarInclusion).comp
      (ContinuousLinearMap.fst ℂ _ _)
  let B : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] Coeff 2 :=
    periodOneDerivative.comp (ContinuousLinearMap.snd ℂ _ _)
  exact analyticAt_const.mul ((Coeff.dualPairing.analyticAt_bilinear (A ab,B ab)).comp
    (f := fun z => (A z,B z)) ((A.analyticAt ab).prod (B.analyticAt ab)))

theorem continuous_periodOneSobolevMomentum : Continuous periodOneSobolevMomentum :=
  continuous_iff_continuousAt.mpr fun ab => (analyticAt_periodOneSobolevMomentum ab).continuousAt

/-- Smooth finite-gap reconstruction identifies this independently defined
physical functional with the second hierarchy Hamiltonian. -/
theorem periodOneSobolevMomentum_sourceFiniteGapSobolevPair
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    periodOneSobolevMomentum (sourceFiniteGapSobolevPair hp hp1 φ hf) =
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2 := by
  have h := periodOneSobolevMomentum_eq_integral
    (sourceFiniteGapSobolevPair hp hp1 φ hf).1 (sourceFiniteGapSobolevPair hp hp1 φ hf).2
  obtain ⟨ha,hb⟩ := periodOneSobolevSynthesis_sourceFiniteGapSobolevPair hp hp1 φ hf
  change _ = -I * ∫ x in (0 : ℝ)..1,
    (fun t : ℝ => periodOneSobolevSynthesis (sourceFiniteGapSobolevPair hp hp1 φ hf).1
      (t : AddCircle (2 : ℝ))) x *
    deriv (fun t : ℝ => periodOneSobolevSynthesis (sourceFiniteGapSobolevPair hp hp1 φ hf).2
      (t : AddCircle (2 : ℝ))) x at h
  rw [ha,hb] at h
  exact h.trans (classicalNLSHamiltonian_two_unsymmetrized _ _).symm

end NLS.ZakharovShabat
