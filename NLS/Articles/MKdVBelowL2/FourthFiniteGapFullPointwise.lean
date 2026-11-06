import NLS.Articles.MKdVBelowL2.FourthFiniteGapFullPhysicalODE
import NLS.Articles.MKdVBelowL2.FourthFiniteGapPointwiseMKdV
import NLS.ZakharovShabat.SourceSobolevPhysicalPhase

/-! # Full pointwise physical fourth equation on actual finite-gap pairs

Both correction terms from H4 - 6H1H2 are retained before restriction to
the smaller scalar diagonal. Physical H¹ time differentiability justifies
the pointwise equation.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.MKdV
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

/-- The physical correction retaining both the mass and momentum terms. -/
def classicalCorrectedFourthField (M P : ℂ) (f g : ℝ → ℂ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  ((classicalRenormalizedFourthField M f g).1 + fun x => 6*P*I*f x,
   (classicalRenormalizedFourthField M f g).2 - fun x => 6*P*I*g x)

/-- Synthesis of the full corrected physical source velocity. -/
theorem periodOneSobolevSynthesis_eq_finiteGapCorrectedFourth
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (M P : ℂ) (v : ScalarDomain 2 × ScalarDomain 2)
    (hv : sobolevSourceInclusion v = sourceFiniteGapPhysicalFourthCoefficients φ hf+
      (6*P) • sourcePhase φ.val - (6*M) • sourceSobolevSpatialDerivative
        (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf)) :
    (fun x : ℝ => periodOneSobolevSynthesis v.1 (x : AddCircle (2:ℝ))) =
      (classicalCorrectedFourthField M P (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1
        (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2).1 ∧
    (fun x : ℝ => periodOneSobolevSynthesis v.2 (x : AddCircle (2:ℝ))) =
      (classicalCorrectedFourthField M P (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1
        (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2).2 := by
  let q := sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  let w := v-(6*P) • sourceSobolevPhase q
  have hw : sobolevSourceInclusion w = sourceFiniteGapPhysicalFourthCoefficients φ hf-
      (6*M) • sourceSobolevSpatialDerivative q := by
    rw [map_sub,map_smul,sobolevSourceInclusion_phase,sobolevSourceInclusion_sourceFiniteGapSobolevPair,hv]
    abel
  have he := periodOneSobolevSynthesis_eq_finiteGapRenormalizedFourth φ hf M w hw
  have hq := periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  constructor
  · funext x
    have h := congrFun he.1 x
    change periodOneSobolevSynthesis (v.1-(6*P) • (sourceSobolevPhase q).1) (x : AddCircle (2:ℝ)) = _ at h
    rw [map_sub,map_smul] at h
    change periodOneSobolevSynthesis v.1 (x : AddCircle (2:ℝ))-
      (6*P)*periodOneSobolevSynthesis (sourceSobolevPhase q).1 (x : AddCircle (2:ℝ)) = _ at h
    rw [(periodOneSobolevSynthesis_phase q x).1,congrFun hq.1 x] at h
    change periodOneSobolevSynthesis v.1 (x : AddCircle (2:ℝ)) = _+6*P*I*_ 
    linear_combination h
  · funext x
    have h := congrFun he.2 x
    change periodOneSobolevSynthesis (v.2-(6*P) • (sourceSobolevPhase q).2) (x : AddCircle (2:ℝ)) = _ at h
    rw [map_sub,map_smul] at h
    change periodOneSobolevSynthesis v.2 (x : AddCircle (2:ℝ))-
      (6*P)*periodOneSobolevSynthesis (sourceSobolevPhase q).2 (x : AddCircle (2:ℝ)) = _ at h
    rw [(periodOneSobolevSynthesis_phase q x).2,congrFun hq.2 x] at h
    change periodOneSobolevSynthesis v.2 (x : AddCircle (2:ℝ)) = _-6*P*I*_
    linear_combination h

/-- Both actual finite-gap physical components solve the complete corrected
fourth equation at every real time and space, without a diagonal hypothesis. -/
theorem hasDerivAt_fourthFiniteGapPhysicalFlow_corrected
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
    let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
    let P := periodOneSobolevMomentum (F.finiteGapSobolevCurve D φ hf time)
    HasDerivAt (fun r => (fourthFiniteGapPhysicalFlow φ hf r).1 x)
      ((classicalCorrectedFourthField (sourceHilbertMass φ.val) P
        (fourthFiniteGapPhysicalFlow φ hf time).1 (fourthFiniteGapPhysicalFlow φ hf time).2).1 x) time ∧
    HasDerivAt (fun r => (fourthFiniteGapPhysicalFlow φ hf r).2 x)
      ((classicalCorrectedFourthField (sourceHilbertMass φ.val) P
        (fourthFiniteGapPhysicalFlow φ hf time).1 (fourthFiniteGapPhysicalFlow φ hf time).2).2 x) time := by
  dsimp only
  let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  let q := F.finiteGapSobolevCurve D φ hf
  have hd : HasDerivAt q (deriv q time) time := (F.differentiable_finiteGapSobolevCurve D φ hf time).hasDerivAt
  have hvel := (F.finiteGapSobolevCurve_deriv_inclusion D φ hf time).trans
    (hasDerivAt_fourthFiniteGapSourceFlow_fullPhysical φ hf time).deriv
  have hphys := periodOneSobolevSynthesis_eq_finiteGapCorrectedFourth _ _ (sourceHilbertMass φ.val)
    (periodOneSobolevMomentum (q time)) (deriv q time) hvel
  let E := (ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).comp periodOneSobolevSynthesis
  have hx := ((E.comp (ContinuousLinearMap.fst ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd
  have hy := ((E.comp (ContinuousLinearMap.snd ℂ (ScalarDomain 2) (ScalarDomain 2))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time hd
  have hfirst : (fun r => periodOneSobolevSynthesis (q r).1 (x : AddCircle (2:ℝ))) =
      fun r => (fourthFiniteGapPhysicalFlow φ hf r).1 x := by
    funext r
    exact congrFun (periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num) _ _).1 x
  have hsecond : (fun r => periodOneSobolevSynthesis (q r).2 (x : AddCircle (2:ℝ))) =
      fun r => (fourthFiniteGapPhysicalFlow φ hf r).2 x := by
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
