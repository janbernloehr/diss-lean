import NLS.Articles.MKdVBelowL2.FourthNativePhysicalField
import NLS.Articles.MKdVBelowL2.FourthSobolevTrajectory
import NLS.Articles.MKdVBelowL2.PhysicalFourthImageIdentities

/-! # The actual physical fourth trajectory on the full H⁴ source

The native Sobolev lift belongs to the fixed physical Birkhoff family.
Bounded physical synthesis gives jointly continuous functions and a jointly
continuous physical velocity. At finite gaps these are the independently
calibrated classical trajectory and its complete corrected field.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

def fourthClassicalSourceFlow (a : FourthClassicalSource) (time : ℝ) : FourthClassicalSource :=
  (fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).sobolevImageFlow
    (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex le_rfl
      (4:ℕ) (Nat.cast_nonneg 4) a time

@[simp] theorem fourthClassicalSourceFlow_zero (a : FourthClassicalSource) :
    fourthClassicalSourceFlow a 0 = a :=
  SourceActionFrequency.sobolevImageFlow_zero _ _ le_rfl _ _ a

theorem originalWeightedRealSource_fourthClassicalSourceFlow (a : FourthClassicalSource) (time : ℝ) :
    originalWeightedRealSource _ (fourthClassicalSourceFlow a time) =
      (fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).imageFlow
        (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
        (originalWeightedRealSource _ a) time :=
  SourceActionFrequency.originalWeightedRealSource_sobolevImageFlow _ _ le_rfl _ _ a time

theorem continuous_fourthClassicalSourceFlow :
    Continuous (fun z : FourthClassicalSource × ℝ => fourthClassicalSourceFlow z.1 z.2) := by
  have h := SourceActionFrequency.continuous_sobolevImageFlow
    (fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num))
    (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex le_rfl (4:ℕ) (Nat.cast_nonneg 4)
  exact h.comp (f := fun z : FourthClassicalSource × ℝ => (z.2,z.1))
    (continuous_snd.prodMk continuous_fst)

def fourthClassicalPhysicalFlow (a : FourthClassicalSource) (time : ℝ) :
    C(AddCircle (2:ℝ),ℂ) × C(AddCircle (2:ℝ),ℂ) :=
  nativeSobolevPhysicalJetCLM 4 0 (by omega) (fourthClassicalSourceFlow a time)

def fourthClassicalPhysicalValue (a : FourthClassicalSource) (time x : ℝ) : ℂ × ℂ :=
  ((fourthClassicalPhysicalFlow a time).1 (x : AddCircle (2:ℝ)),
   (fourthClassicalPhysicalFlow a time).2 (x : AddCircle (2:ℝ)))

def fourthClassicalPhysicalVelocity (a : FourthClassicalSource) (time x : ℝ) : ℂ × ℂ :=
  ((fourthClassicalVelocity a (fourthClassicalSourceFlow a time)).1 (x : AddCircle (2:ℝ)),
   (fourthClassicalVelocity a (fourthClassicalSourceFlow a time)).2 (x : AddCircle (2:ℝ)))

theorem continuous_fourthClassicalPhysicalValue (x : ℝ) :
    Continuous (fun z : FourthClassicalSource × ℝ => fourthClassicalPhysicalValue z.1 z.2 x) := by
  have hc := (nativeSobolevPhysicalJetCLM 4 0 (by omega)).continuous.comp continuous_fourthClassicalSourceFlow
  exact ((ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).continuous.comp hc.fst).prodMk
    ((ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).continuous.comp hc.snd)

theorem continuous_fourthClassicalPhysicalVelocity (x : ℝ) :
    Continuous (fun z : FourthClassicalSource × ℝ => fourthClassicalPhysicalVelocity z.1 z.2 x) := by
  have hc := continuous_fourthClassicalVelocity.comp
    ((continuous_fst : Continuous (fun z : FourthClassicalSource × ℝ => z.1)).prodMk continuous_fourthClassicalSourceFlow)
  exact ((ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).continuous.comp hc.fst).prodMk
    ((ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).continuous.comp hc.snd)

theorem fourthClassicalSourceFlow_finiteGap (a : FourthClassicalSource)
    (hf : originalWeightedRealSource _ a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    originalWeightedRealSource _ (fourthClassicalSourceFlow a time) ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
  rw [originalWeightedRealSource_fourthClassicalSourceFlow]
  exact SourceActionFrequency.imageFlow_finiteGap _ _ _ hf time
    (SourceActionFrequency.mem_imageDomain_of_le_two _ _ le_rfl _ time)

theorem fourthClassicalPhysicalValue_eq_finiteGap (a : FourthClassicalSource)
    (hf : originalWeightedRealSource _ a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    fourthClassicalPhysicalValue a time x =
      ((fourthFiniteGapPhysicalFlow (originalWeightedRealSource _ a) hf time).1 x,
       (fourthFiniteGapPhysicalFlow (originalWeightedRealSource _ a) hf time).2 x) := by
  have he := nativeSobolevPhysicalJet_eq_finiteGap 4 0 (by omega) (fourthClassicalSourceFlow a time)
    (fourthClassicalSourceFlow_finiteGap a hf time)
  have hpair := congrArg₂ Prod.mk (congrFun he.1 x) (congrFun he.2 x)
  simpa only [fourthClassicalPhysicalValue,fourthClassicalPhysicalFlow,fourthFiniteGapPhysicalFlow,
    originalWeightedRealSource_fourthClassicalSourceFlow,iteratedDeriv_zero] using! hpair

theorem fourthClassicalMomentum_flow_eq_finiteGap (a : FourthClassicalSource)
    (hf : originalWeightedRealSource _ a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    fourthClassicalMomentum (fourthClassicalSourceFlow a time) =
      periodOneSobolevMomentum
        ((fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).finiteGapSobolevCurve
          (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
          (originalWeightedRealSource _ a) hf time) := by
  have he := nativeSobolevH1PairCLM_eq_finiteGap 4 (by omega) (fourthClassicalSourceFlow a time)
    (fourthClassicalSourceFlow_finiteGap a hf time)
  simpa only [fourthClassicalMomentum,SourceActionFrequency.finiteGapSobolevCurve,
    originalWeightedRealSource_fourthClassicalSourceFlow] using congrArg periodOneSobolevMomentum he

/-- The physical representatives retain every original signed Fourier coefficient. -/
theorem periodOneCoefficient_fourthClassicalPhysicalValue (a : FourthClassicalSource) (time : ℝ) (n : ℤ) :
    periodOneCoefficient (fun x => (fourthClassicalPhysicalValue a time x).1) n =
      (originalWeightedRealSource _ (fourthClassicalSourceFlow a time)).val.fst n ∧
    periodOneCoefficient (fun x => (fourthClassicalPhysicalValue a time x).2) n =
      (originalWeightedRealSource _ (fourthClassicalSourceFlow a time)).val.snd n := by
  let b := fourthClassicalSourceFlow a time
  let q := nativeSobolevH1PairCLM 4 (by omega) b
  have h1 : (fun x => (fourthClassicalPhysicalValue a time x).1) =
      (fun x : ℝ => periodOneSobolevSynthesis q.1 (x : AddCircle (2:ℝ))) :=
    funext (fun x => (nativeSobolevPhysicalJet_zero_eq_synthesis 4 (by omega) b x).1)
  have h2 : (fun x => (fourthClassicalPhysicalValue a time x).2) =
      (fun x : ℝ => periodOneSobolevSynthesis q.2 (x : AddCircle (2:ℝ))) :=
    funext (fun x => (nativeSobolevPhysicalJet_zero_eq_synthesis 4 (by omega) b x).2)
  have he := sobolevSourceInclusion_nativeSobolevH1PairCLM 4 (by omega) b
  constructor
  · rw [h1,periodOneCoefficient_periodOneSobolevSynthesis]
    simpa only [sobolevSourceInclusion_fst] using congrArg (fun z : CoeffPair 2 => z.fst n) he
  · rw [h2,periodOneCoefficient_periodOneSobolevSynthesis]
    simpa only [sobolevSourceInclusion_snd] using congrArg (fun z : CoeffPair 2 => z.snd n) he

/-- These physical functions have exactly the Fourier coefficients of the
actual original distribution lift of the same fixed Theorem 1.2 family. -/
theorem fourthClassicalPhysicalValue_physical_coefficients (a : FourthClassicalSource) (time : ℝ) (n : ℤ) :
    let u := fourthPhysicalImageFlow (p := 2) (by simp) (by norm_num)
      (physicalRealCoefficientsCL.symm (originalWeightedRealSource _ a)) time
    periodOneCoefficient (fun x => (fourthClassicalPhysicalValue a time x).1) n =
      u.val.1.val (NLS.Fourier.SmoothPeriodicTest.mode (-n)) ∧
    periodOneCoefficient (fun x => (fourthClassicalPhysicalValue a time x).2) n =
      u.val.2.val (NLS.Fourier.SmoothPeriodicTest.mode (-n)) := by
  dsimp only
  let u := fourthPhysicalImageFlow (p := 2) (by simp) (by norm_num)
    (physicalRealCoefficientsCL.symm (originalWeightedRealSource _ a)) time
  have he := fourthPhysicalImageFlow_coefficients (p := 2) (by simp) (by norm_num)
    (physicalRealCoefficientsCL.symm (originalWeightedRealSource _ a)) time
  rw [ContinuousLinearEquiv.apply_symm_apply] at he
  have he' : physicalRealCoefficientsCL u = originalWeightedRealSource _ (fourthClassicalSourceFlow a time) :=
    he.trans (originalWeightedRealSource_fourthClassicalSourceFlow a time).symm
  have hc := periodOneCoefficient_fourthClassicalPhysicalValue a time n
  exact ⟨hc.1.trans ((congrArg (fun z : realTypeSourceSubmodule 2 => z.val.fst n) he').symm.trans
      (physicalCoefficients_apply u.val n).1),
    hc.2.trans ((congrArg (fun z : realTypeSourceSubmodule 2 => z.val.snd n) he').symm.trans
      (physicalCoefficients_apply u.val n).2)⟩

end NLS.Articles.MKdVBelowL2
