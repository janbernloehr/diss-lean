import NLS.Articles.MKdVBelowL2.FourthFiniteGapRenormalizedODE
import NLS.Articles.MKdVBelowL2.ClassicalRenormalizedFourthRegularity
import NLS.ZakharovShabat.SourceActionPhaseSobolevTime
import NLS.Fourier.PeriodOneFourierUniqueness
import NLS.ZakharovShabat.SourceFiniteGapNLSVariation

/-! # The actual finite-gap fourth trajectory solves renormalized mKdV pointwise

The canonical H¹ time derivative and original Fourier coefficient uniqueness
identify the physical source velocity with the certified renormalized field.
Bounded spatial evaluation gives the actual pointwise time equation. The
equal-field diagonal then gives the scalar cubic mKdV expression.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.MKdV
open scoped ContDiff
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

/-- The H¹ representative of the calibrated renormalized source velocity
synthesizes to exactly the physical differential field at every point. -/
theorem periodOneSobolevSynthesis_eq_finiteGapRenormalizedFourth
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (M : ℂ) (v : ScalarDomain 2 × ScalarDomain 2)
    (hv : sobolevSourceInclusion v = sourceFiniteGapPhysicalFourthCoefficients φ hf-
      (6*M) • sourceSobolevSpatialDerivative (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf)) :
    (fun x : ℝ => periodOneSobolevSynthesis v.1 (x : AddCircle (2:ℝ))) =
      (classicalRenormalizedFourthField M (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1
        (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2).1 ∧
    (fun x : ℝ => periodOneSobolevSynthesis v.2 (x : AddCircle (2:ℝ))) =
      (classicalRenormalizedFourthField M (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1
        (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2).2 := by
  let f := (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1
  let g := (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2
  have hs := contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf
  have hp := periodic_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf
  have hreg := classicalRenormalizedFourthField_regular M f g hs.1 hs.2 hp.1 hp.2
  have hc := classicalRenormalizedFourthField_coefficients M f g hs.1 hs.2 hp.1 hp.2
  have hH1 := sobolevSourceInclusion_sourceFiniteGapSobolevPair φ hf
  constructor
  · apply periodOneSobolevSynthesis_eq_of_coefficients v.1 _ hreg.1.1.continuous hreg.2.1
    intro n
    have h := congrArg (fun a : CoeffPair 2 => a.fst n) hv
    change (sobolevSourceInclusion v).fst n = (sourceFiniteGapPhysicalFourthCoefficients φ hf).fst n-
      (6*M)*(sourceSobolevSpatialDerivative (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf)).fst n at h
    rw [sobolevSourceInclusion_fst,(sourceFiniteGapPhysicalFourthCoefficients_apply φ hf n).1,
      sourceSobolevSpatialDerivative_fst,periodOneDerivative_apply] at h
    have he := congrArg (fun a : CoeffPair 2 => a.fst n) hH1
    rw [sobolevSourceInclusion_fst] at he
    rw [he,← (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf n).1] at h
    exact h.trans (hc n).1.symm
  · apply periodOneSobolevSynthesis_eq_of_coefficients v.2 _ hreg.1.2.continuous hreg.2.2
    intro n
    have h := congrArg (fun a : CoeffPair 2 => a.snd n) hv
    change (sobolevSourceInclusion v).snd n = (sourceFiniteGapPhysicalFourthCoefficients φ hf).snd n-
      (6*M)*(sourceSobolevSpatialDerivative (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf)).snd n at h
    rw [sobolevSourceInclusion_snd,(sourceFiniteGapPhysicalFourthCoefficients_apply φ hf n).2,
      sourceSobolevSpatialDerivative_snd,periodOneDerivative_apply] at h
    have he := congrArg (fun a : CoeffPair 2 => a.snd n) hH1
    rw [sobolevSourceInclusion_snd] at he
    rw [he,← (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf n).2] at h
    exact h.trans (hc n).2.symm

/-- The actual physical finite-gap trajectory of the fixed fourth family. -/
def fourthFiniteGapPhysicalFlow (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  sourceFiniteGapPhysicalPair (by simp) (by norm_num) (F.imageFlow D φ time)
    (F.imageFlow_finiteGap D φ hf time (F.mem_imageDomain_of_le_two D le_rfl φ time))

@[simp] theorem fourthFiniteGapPhysicalFlow_zero (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    fourthFiniteGapPhysicalFlow φ hf 0 = sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf := by
  unfold fourthFiniteGapPhysicalFlow
  simp only [SourceActionFrequency.imageFlow_zero]

/-- Both actual pointwise time derivatives are the physical renormalized
fourth field, with the conserved initial physical mass and exact sign. -/
theorem hasDerivAt_fourthFiniteGapPhysicalFlow_renormalized
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hφ : φ.val.fst = φ.val.snd) (time x : ℝ) :
    HasDerivAt (fun r => (fourthFiniteGapPhysicalFlow φ hf r).1 x)
      ((classicalRenormalizedFourthField (sourceHilbertMass φ.val)
        (fourthFiniteGapPhysicalFlow φ hf time).1 (fourthFiniteGapPhysicalFlow φ hf time).2).1 x) time ∧
    HasDerivAt (fun r => (fourthFiniteGapPhysicalFlow φ hf r).2 x)
      ((classicalRenormalizedFourthField (sourceHilbertMass φ.val)
        (fourthFiniteGapPhysicalFlow φ hf time).1 (fourthFiniteGapPhysicalFlow φ hf time).2).2 x) time := by
  let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  let q := F.finiteGapSobolevCurve D φ hf
  have hd : HasDerivAt q (deriv q time) time := (F.differentiable_finiteGapSobolevCurve D φ hf time).hasDerivAt
  have hvel := (F.finiteGapSobolevCurve_deriv_inclusion D φ hf time).trans
    (hasDerivAt_fourthFiniteGapSourceFlow_renormalized φ hf hφ time).deriv
  have hphys := periodOneSobolevSynthesis_eq_finiteGapRenormalizedFourth _ _ (sourceHilbertMass φ.val) (deriv q time) hvel
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

/-- The smooth physical fields of the actual smaller-diagonal trajectory
are equal as functions, not just as spectral actions. -/
theorem fourthFiniteGapPhysicalFlow_diagonal (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (hφ : φ.val.fst = φ.val.snd) (time : ℝ) :
    (fourthFiniteGapPhysicalFlow φ hf time).1 = (fourthFiniteGapPhysicalFlow φ hf time).2 := by
  let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  let ψ := F.imageFlow D φ time
  have hfψ := F.imageFlow_finiteGap D φ hf time (F.mem_imageDomain_of_le_two D le_rfl φ time)
  have hdiag := fourthHilbertImageFlow_preserves_diagonal φ hφ time
  have hs := contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) ψ hfψ
  have hp := periodic_sourceFiniteGapPhysicalPair (by simp) (by norm_num) ψ hfψ
  apply eq_of_periodOneCoefficient_eq _ _ hs.1.continuous hs.2.continuous hp.1 hp.2
  intro n
  have hc := periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) ψ hfψ n
  exact hc.1.trans ((congrArg (fun c : Coeff 2 => c n) hdiag).trans hc.2.symm)

/-- The actual scalar physical mKdV field is real at every time and point,
from its original real source form and its actual equal-field identity. -/
theorem fourthFiniteGapPhysicalFlow_im_eq_zero (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (hφ : φ.val.fst = φ.val.snd) (time x : ℝ) :
    ((fourthFiniteGapPhysicalFlow φ hf time).1 x).im = 0 := by
  let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  have hfψ := F.imageFlow_finiteGap D φ hf time (F.mem_imageDomain_of_le_two D le_rfl φ time)
  have hr := sourceFiniteGapPhysicalPair_real (by simp) (by norm_num) (F.imageFlow D φ time) hfψ x
  have hd := congrFun (fourthFiniteGapPhysicalFlow_diagonal φ hf hφ time) x
  have hc : starRingEnd ℂ ((fourthFiniteGapPhysicalFlow φ hf time).1 x) =
      (fourthFiniteGapPhysicalFlow φ hf time).1 x := hr.symm.trans hd.symm
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

/-- The constant in the actual scalar PDE is exactly the original unit-
period integral of the square of its initial physical field. -/
theorem fourthFiniteGapMass_eq_integral_square (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (hφ : φ.val.fst = φ.val.snd) :
    sourceHilbertMass φ.val = ∫ x in (0:ℝ)..1, ((fourthFiniteGapPhysicalFlow φ hf 0).1 x)^2 := by
  have hm : (∫ x in (0:ℝ)..1, (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 x*
      (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2 x) = sourceHilbertMass φ.val := by
    simpa only [sourceFiniteGapNLSHamiltonian,classicalNLSHamiltonian_one,sourceHilbertMass,
      NLS.Poisson.reflectedHilbertPairing_apply] using sourceFiniteGapNLSHamiltonian_one (by simp) (by norm_num) φ hf
  have hd := fourthFiniteGapPhysicalFlow_diagonal φ hf hφ 0
  rw [fourthFiniteGapPhysicalFlow_zero] at hd
  rw [← hd] at hm
  simpa only [fourthFiniteGapPhysicalFlow_zero,pow_two] using hm.symm

/-- The actual finite-gap first component solves the scalar renormalized
mKdV equation at every real time and every spatial point. -/
theorem hasDerivAt_fourthFiniteGapPhysicalFlow_mKdV
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hφ : φ.val.fst = φ.val.snd) (time x : ℝ) :
    HasDerivAt (fun r => (fourthFiniteGapPhysicalFlow φ hf r).1 x)
      (-deriv (deriv (deriv (fourthFiniteGapPhysicalFlow φ hf time).1)) x+
        6*(((fourthFiniteGapPhysicalFlow φ hf time).1 x)^2-sourceHilbertMass φ.val)*
          deriv (fourthFiniteGapPhysicalFlow φ hf time).1 x) time := by
  have hd := (hasDerivAt_fourthFiniteGapPhysicalFlow_renormalized φ hf hφ time x).1
  rw [← fourthFiniteGapPhysicalFlow_diagonal φ hf hφ time,classicalRenormalizedFourthField_diagonal] at hd
  exact hd

end NLS.Articles.MKdVBelowL2
