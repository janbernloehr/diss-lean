import NLS.Articles.MKdVBelowL2.OrdinaryFourthFiniteGapPointwise
import NLS.Articles.MKdVBelowL2.ScalarSmoothMassPhases

/-! # The actual mass-restored fourth trajectory on the native H⁴ source

The source lift, its physical fields and its complete physical velocity are
jointly continuous. The velocity uses zero mass and retains the current
momentum phase on general real-type pairs.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

def ordinaryFourthClassicalSourceFlow (a : FourthClassicalSource) (time : ℝ) : FourthClassicalSource :=
  (ordinaryFourthSourcePhaseFrequency).sobolevImageFlow
    (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex le_rfl
      (4:ℕ) (Nat.cast_nonneg 4) a time

@[simp] theorem ordinaryFourthClassicalSourceFlow_zero (a : FourthClassicalSource) :
    ordinaryFourthClassicalSourceFlow a 0 = a :=
  SourceActionFrequency.sobolevImageFlow_zero _ _ le_rfl _ _ a

theorem originalWeightedRealSource_ordinaryFourthClassicalSourceFlow (a : FourthClassicalSource) (time : ℝ) :
    originalWeightedRealSource _ (ordinaryFourthClassicalSourceFlow a time) =
      (ordinaryFourthSourcePhaseFrequency).imageFlow
        (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
        (originalWeightedRealSource _ a) time :=
  SourceActionFrequency.originalWeightedRealSource_sobolevImageFlow _ _ le_rfl _ _ a time

theorem continuous_ordinaryFourthClassicalSourceFlow :
    Continuous (fun z : FourthClassicalSource × ℝ => ordinaryFourthClassicalSourceFlow z.1 z.2) := by
  have h := SourceActionFrequency.continuous_sobolevImageFlow
    (ordinaryFourthSourcePhaseFrequency)
    (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex le_rfl (4:ℕ) (Nat.cast_nonneg 4)
  exact h.comp (f := fun z : FourthClassicalSource × ℝ => (z.2,z.1))
    (continuous_snd.prodMk continuous_fst)

def ordinaryFourthClassicalPhysicalFlow (a : FourthClassicalSource) (time : ℝ) :
    C(AddCircle (2:ℝ),ℂ) × C(AddCircle (2:ℝ),ℂ) :=
  nativeSobolevPhysicalJetCLM 4 0 (by omega) (ordinaryFourthClassicalSourceFlow a time)

def ordinaryFourthClassicalPhysicalValue (a : FourthClassicalSource) (time x : ℝ) : ℂ × ℂ :=
  ((ordinaryFourthClassicalPhysicalFlow a time).1 (x : AddCircle (2:ℝ)),
   (ordinaryFourthClassicalPhysicalFlow a time).2 (x : AddCircle (2:ℝ)))

def ordinaryFourthClassicalPhysicalVelocity (a : FourthClassicalSource) (time x : ℝ) : ℂ × ℂ :=
  ((fourthClassicalVelocity 0 (ordinaryFourthClassicalSourceFlow a time)).1 (x : AddCircle (2:ℝ)),
   (fourthClassicalVelocity 0 (ordinaryFourthClassicalSourceFlow a time)).2 (x : AddCircle (2:ℝ)))

theorem continuous_ordinaryFourthClassicalPhysicalValue (x : ℝ) :
    Continuous (fun z : FourthClassicalSource × ℝ => ordinaryFourthClassicalPhysicalValue z.1 z.2 x) := by
  have hc := (nativeSobolevPhysicalJetCLM 4 0 (by omega)).continuous.comp continuous_ordinaryFourthClassicalSourceFlow
  exact ((ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).continuous.comp hc.fst).prodMk
    ((ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).continuous.comp hc.snd)

theorem continuous_ordinaryFourthClassicalPhysicalVelocity (x : ℝ) :
    Continuous (fun z : FourthClassicalSource × ℝ => ordinaryFourthClassicalPhysicalVelocity z.1 z.2 x) := by
  have hc := continuous_fourthClassicalVelocity.comp
    ((continuous_const : Continuous (fun _ : FourthClassicalSource × ℝ => (0:FourthClassicalSource))).prodMk continuous_ordinaryFourthClassicalSourceFlow)
  exact ((ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).continuous.comp hc.fst).prodMk
    ((ContinuousMap.evalCLM ℂ (x : AddCircle (2:ℝ))).continuous.comp hc.snd)

theorem ordinaryFourthClassicalSourceFlow_finiteGap (a : FourthClassicalSource)
    (hf : originalWeightedRealSource _ a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    originalWeightedRealSource _ (ordinaryFourthClassicalSourceFlow a time) ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
  rw [originalWeightedRealSource_ordinaryFourthClassicalSourceFlow]
  exact SourceActionFrequency.imageFlow_finiteGap _ _ _ hf time
    (SourceActionFrequency.mem_imageDomain_of_le_two _ _ le_rfl _ time)

theorem ordinaryFourthClassicalPhysicalValue_eq_finiteGap (a : FourthClassicalSource)
    (hf : originalWeightedRealSource _ a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time x : ℝ) :
    ordinaryFourthClassicalPhysicalValue a time x =
      ((ordinaryFourthFiniteGapPhysicalFlow (originalWeightedRealSource _ a) hf time).1 x,
       (ordinaryFourthFiniteGapPhysicalFlow (originalWeightedRealSource _ a) hf time).2 x) := by
  have he := nativeSobolevPhysicalJet_eq_finiteGap 4 0 (by omega) (ordinaryFourthClassicalSourceFlow a time)
    (ordinaryFourthClassicalSourceFlow_finiteGap a hf time)
  have hpair := congrArg₂ Prod.mk (congrFun he.1 x) (congrFun he.2 x)
  simpa only [ordinaryFourthClassicalPhysicalValue,ordinaryFourthClassicalPhysicalFlow,ordinaryFourthFiniteGapPhysicalFlow,
    originalWeightedRealSource_ordinaryFourthClassicalSourceFlow,iteratedDeriv_zero] using! hpair

theorem ordinaryFourthClassicalMomentum_flow_eq_finiteGap (a : FourthClassicalSource)
    (hf : originalWeightedRealSource _ a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    fourthClassicalMomentum (ordinaryFourthClassicalSourceFlow a time) =
      periodOneSobolevMomentum
        ((ordinaryFourthSourcePhaseFrequency).finiteGapSobolevCurve
          (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
          (originalWeightedRealSource _ a) hf time) := by
  have he := nativeSobolevH1PairCLM_eq_finiteGap 4 (by omega) (ordinaryFourthClassicalSourceFlow a time)
    (ordinaryFourthClassicalSourceFlow_finiteGap a hf time)
  simpa only [fourthClassicalMomentum,SourceActionFrequency.finiteGapSobolevCurve,
    originalWeightedRealSource_ordinaryFourthClassicalSourceFlow] using congrArg periodOneSobolevMomentum he

@[simp] theorem fourthClassicalMass_zero : fourthClassicalMass (0:FourthClassicalSource) = 0 := by
  rw [fourthClassicalMass_eq_norm_fst]
  have he : originalWeightedRealSource _ (0:FourthClassicalSource) = 0 :=
    (originalWeightedRealSourceCLM (p := 2) (sourceSobolevSpectralWeight (4:ℕ) (Nat.cast_nonneg 4))).map_zero
  rw [he]
  simp

end NLS.Articles.MKdVBelowL2
