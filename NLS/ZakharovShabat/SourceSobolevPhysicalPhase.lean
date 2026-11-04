import NLS.ZakharovShabat.SourcePhaseCompatibility
import NLS.ZakharovShabat.SourceSobolevEmbedding
import NLS.Fourier.PeriodOneSobolev

/-! # The original component phase on physical H¹ representatives -/
noncomputable section
set_option autoImplicit false
open Complex NLS.Fourier
namespace NLS.ZakharovShabat

def sourceSobolevPhase : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] (ScalarDomain 2 × ScalarDomain 2) :=
  (I • ContinuousLinearMap.id ℂ (ScalarDomain 2)).prodMap
    ((-I) • ContinuousLinearMap.id ℂ (ScalarDomain 2))

theorem sobolevSourceInclusion_phase (q : ScalarDomain 2 × ScalarDomain 2) :
    sobolevSourceInclusion (sourceSobolevPhase q) = sourcePhase (sobolevSourceInclusion q) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n
  · change (sobolevSourceInclusion (sourceSobolevPhase q)).fst n =
      (sourcePhase (sobolevSourceInclusion q)).fst n
    rw [sobolevSourceInclusion_fst,sourcePhase_fst]
    change I*q.1.val n = I*(sobolevSourceInclusion q).fst n
    rw [sobolevSourceInclusion_fst]
  · change (sobolevSourceInclusion (sourceSobolevPhase q)).snd n =
      (sourcePhase (sobolevSourceInclusion q)).snd n
    rw [sobolevSourceInclusion_snd,sourcePhase_snd]
    change -I*q.2.val n = -I*(sobolevSourceInclusion q).snd n
    rw [sobolevSourceInclusion_snd]

theorem periodOneSobolevSynthesis_phase (q : ScalarDomain 2 × ScalarDomain 2) (x : ℝ) :
    periodOneSobolevSynthesis (sourceSobolevPhase q).1 (x : AddCircle (2:ℝ)) =
      I*periodOneSobolevSynthesis q.1 (x : AddCircle (2:ℝ)) ∧
    periodOneSobolevSynthesis (sourceSobolevPhase q).2 (x : AddCircle (2:ℝ)) =
      -I*periodOneSobolevSynthesis q.2 (x : AddCircle (2:ℝ)) := by
  constructor <;> simp [sourceSobolevPhase]

end NLS.ZakharovShabat
