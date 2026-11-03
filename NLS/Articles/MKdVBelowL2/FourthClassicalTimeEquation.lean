import NLS.Articles.MKdVBelowL2.FourthClassicalPhysicalFlow

/-! # The actual fourth trajectory satisfies its physical equation on H⁴

The full finite-gap equation is extended through joint continuity of the
actual paths and velocities. Normalized source coordinates keep the dense
parameter limit in a fixed Hilbert space. No diagonal approximation or
extra time-derivative hypothesis is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

theorem fourthClassicalPhysicalVelocity_eq_finiteGap (a : FourthClassicalSource)
    (hf : originalWeightedRealSource _ a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
    let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
    let φ := originalWeightedRealSource _ a
    let P := periodOneSobolevMomentum (F.finiteGapSobolevCurve D φ hf time)
    fourthClassicalPhysicalVelocity a time x =
      ((classicalCorrectedFourthField (sourceHilbertMass φ.val) P
        (fourthFiniteGapPhysicalFlow φ hf time).1 (fourthFiniteGapPhysicalFlow φ hf time).2).1 x,
       (classicalCorrectedFourthField (sourceHilbertMass φ.val) P
        (fourthFiniteGapPhysicalFlow φ hf time).1 (fourthFiniteGapPhysicalFlow φ hf time).2).2 x) := by
  dsimp only
  have he := fourthClassicalVelocity_eq_classical a (fourthClassicalSourceFlow a time) x
  dsimp only at he
  have h1 : (fun y : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega)
      (fourthClassicalSourceFlow a time)).1 (y : AddCircle (2:ℝ))) =
      (fourthFiniteGapPhysicalFlow (originalWeightedRealSource _ a) hf time).1 := by
    funext y
    exact congrArg Prod.fst (fourthClassicalPhysicalValue_eq_finiteGap a hf time y)
  have h2 : (fun y : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega)
      (fourthClassicalSourceFlow a time)).2 (y : AddCircle (2:ℝ))) =
      (fourthFiniteGapPhysicalFlow (originalWeightedRealSource _ a) hf time).2 := by
    funext y
    exact congrArg Prod.snd (fourthClassicalPhysicalValue_eq_finiteGap a hf time y)
  rw [h1,h2,fourthClassicalMomentum_flow_eq_finiteGap a hf time] at he
  exact Prod.ext he.1 he.2

theorem hasDerivAt_fourthClassicalPhysicalValue_finiteGap (a : FourthClassicalSource)
    (hf : originalWeightedRealSource _ a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    HasDerivAt (fun r => fourthClassicalPhysicalValue a r x)
      (fourthClassicalPhysicalVelocity a time x) time := by
  have hd := hasDerivAt_fourthFiniteGapPhysicalFlow_corrected (originalWeightedRealSource _ a) hf time x
  dsimp only at hd
  have hp := hd.1.prodMk hd.2
  have he : (fun r => fourthClassicalPhysicalValue a r x) =
      (fun r => ((fourthFiniteGapPhysicalFlow (originalWeightedRealSource _ a) hf r).1 x,
        (fourthFiniteGapPhysicalFlow (originalWeightedRealSource _ a) hf r).2 x)) :=
    funext (fun r => fourthClassicalPhysicalValue_eq_finiteGap a hf r x)
  rw [← he,← fourthClassicalPhysicalVelocity_eq_finiteGap a hf time x] at hp
  exact hp

private theorem hasDerivAt_fourthClassicalPhysicalValue_normalized
    (b : realTypeSourceSubmodule 2) (time x : ℝ) :
    let a := (weightedRealSourceEquiv (p := 2)
      (sourceSobolevSpectralWeight (4:ℕ) (Nat.cast_nonneg 4))).symm b
    HasDerivAt (fun r => fourthClassicalPhysicalValue a r x)
      (fourthClassicalPhysicalVelocity a time x) time := by
  let w := sourceSobolevSpectralWeight (4:ℕ) (Nat.cast_nonneg 4)
  let e := (weightedRealSourceEquiv (p := 2) w).symm
  have he : Continuous (fun z : realTypeSourceSubmodule 2 × ℝ => (e z.1,z.2)) :=
    (e.continuous.comp continuous_fst).prodMk continuous_snd
  exact NLS.FunctionalAnalysis.hasDerivAt_of_dense_parameters _
    (dense_normalizedWeightedRealSource_finiteGap (by simp) (by norm_num) w) _ _
    ((continuous_fourthClassicalPhysicalValue x).comp he)
    ((continuous_fourthClassicalPhysicalVelocity x).comp he)
    (fun c hc r => hasDerivAt_fourthClassicalPhysicalValue_finiteGap (e c)
      (by change normalizedWeightedRealSourceLp w (weightedRealSourceEquiv w (e c)) ∈ _
          rw [ContinuousLinearEquiv.apply_symm_apply]
          exact hc) r x) b time

/-- Every original real H⁴ input has the actual complete pointwise fourth
time equation at every real time and spatial point. -/
theorem hasDerivAt_fourthClassicalPhysicalValue (a : FourthClassicalSource) (time x : ℝ) :
    HasDerivAt (fun r => fourthClassicalPhysicalValue a r x)
      (fourthClassicalPhysicalVelocity a time x) time := by
  have h := hasDerivAt_fourthClassicalPhysicalValue_normalized (weightedRealSourceEquiv _ a) time x
  dsimp only at h
  rw [ContinuousLinearEquiv.symm_apply_apply] at h
  exact h

end NLS.Articles.MKdVBelowL2
