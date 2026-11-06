import NLS.Articles.MKdVBelowL2.OrdinaryFourthFiniteGapPhysicalODE
import NLS.Articles.MKdVBelowL2.FourthFiniteGapFullPointwise

/-! # Pointwise physical equation of the mass-restored finite-gap fourth flow -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.MKdV
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

def ordinaryFourthFiniteGapPhysicalFlow (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  let F := ordinaryFourthSourcePhaseFrequency
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  sourceFiniteGapPhysicalPair (by simp) (by norm_num) (F.imageFlow D φ time)
    (F.imageFlow_finiteGap D φ hf time (F.mem_imageDomain_of_le_two D le_rfl φ time))

/-- Both actual finite-gap physical components solve the complete corrected
fourth equation at every real time and space, without a diagonal hypothesis. -/
theorem hasDerivAt_ordinaryFourthFiniteGapPhysicalFlow_corrected
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    let F := ordinaryFourthSourcePhaseFrequency
    let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
    let P := periodOneSobolevMomentum (F.finiteGapSobolevCurve D φ hf time)
    HasDerivAt (fun r => (ordinaryFourthFiniteGapPhysicalFlow φ hf r).1 x)
      ((classicalCorrectedFourthField (0:ℂ) P
        (ordinaryFourthFiniteGapPhysicalFlow φ hf time).1 (ordinaryFourthFiniteGapPhysicalFlow φ hf time).2).1 x) time ∧
    HasDerivAt (fun r => (ordinaryFourthFiniteGapPhysicalFlow φ hf r).2 x)
      ((classicalCorrectedFourthField (0:ℂ) P
        (ordinaryFourthFiniteGapPhysicalFlow φ hf time).1 (ordinaryFourthFiniteGapPhysicalFlow φ hf time).2).2 x) time := by
  dsimp only
  let F := ordinaryFourthSourcePhaseFrequency
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  let q := F.finiteGapSobolevCurve D φ hf
  have hd : HasDerivAt q (deriv q time) time := (F.differentiable_finiteGapSobolevCurve D φ hf time).hasDerivAt
  have hvel := (F.finiteGapSobolevCurve_deriv_inclusion D φ hf time).trans
    (hasDerivAt_ordinaryFourthFiniteGapSourceFlow_physical φ hf time).deriv
  have hv : sobolevSourceInclusion (deriv q time) =
      sourceFiniteGapPhysicalFourthCoefficients (F.imageFlow D φ time)
        (F.imageFlow_finiteGap D φ hf time (F.mem_imageDomain_of_le_two D le_rfl φ time))+
        (6*periodOneSobolevMomentum (q time)) • sourcePhase (F.imageFlow D φ time).val-
        (6*(0:ℂ)) • sourceSobolevSpatialDerivative (q time) := by
    simpa only [mul_zero,zero_smul,sub_zero] using! hvel
  have hphys := periodOneSobolevSynthesis_eq_finiteGapCorrectedFourth _ _ (0:ℂ)
    (periodOneSobolevMomentum (q time)) (deriv q time) hv
  let E := (ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).comp periodOneSobolevSynthesis
  have hx := ((E.comp (ContinuousLinearMap.fst ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd
  have hy := ((E.comp (ContinuousLinearMap.snd ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd
  have hfirst : (fun r => periodOneSobolevSynthesis (q r).1 (x : AddCircle (2:ℝ))) =
      fun r => (ordinaryFourthFiniteGapPhysicalFlow φ hf r).1 x := by
    funext r
    exact congrFun (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num) _ _).1 x
  have hsecond : (fun r => periodOneSobolevSynthesis (q r).2 (x : AddCircle (2:ℝ))) =
      fun r => (ordinaryFourthFiniteGapPhysicalFlow φ hf r).2 x := by
    funext r
    exact congrFun (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num) _ _).2 x
  change HasDerivAt (fun r => periodOneSobolevSynthesis (q r).1 (x : AddCircle (2:ℝ)))
    (periodOneSobolevSynthesis (deriv q time).1 (x : AddCircle (2:ℝ))) time at hx
  change HasDerivAt (fun r => periodOneSobolevSynthesis (q r).2 (x : AddCircle (2:ℝ)))
    (periodOneSobolevSynthesis (deriv q time).2 (x : AddCircle (2:ℝ))) time at hy
  rw [hfirst,congrFun hphys.1 x] at hx
  rw [hsecond,congrFun hphys.2 x] at hy
  exact ⟨hx,hy⟩

end NLS.Articles.MKdVBelowL2
