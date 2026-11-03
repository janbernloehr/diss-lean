import NLS.Articles.MKdVBelowL2.FourthFiniteGapFullPointwise
import NLS.ZakharovShabat.SourceNativeSobolevPhysicalJets
import NLS.ZakharovShabat.SourceNativeSobolevH1Pair
import NLS.ZakharovShabat.SourceWeightedRealSourceInclusion

/-! # Continuous physical corrected fourth field on the full H⁴ source

The third spatial jet has a continuous physical representative. The actual
mass and momentum retain their independent physical definitions. This
continuous field is suitable for passage from finite-gap trajectories.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier NLS.MKdV
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

/-- Native physical H⁴ regularity, sufficient for all three classical jets. -/
abbrev FourthClassicalSource := weightedRealSourceSubmodule (p := 2)
  (sourceSobolevSpectralWeight (4:ℕ) (Nat.cast_nonneg 4))

def fourthClassicalMass (a : FourthClassicalSource) : ℂ :=
  sourceHilbertMass (originalWeightedRealSource _ a).val

def fourthClassicalMomentum (a : FourthClassicalSource) : ℂ :=
  periodOneSobolevMomentum (nativeSobolevH1PairCLM 4 (by omega) a)

theorem continuous_fourthClassicalMass : Continuous fourthClassicalMass :=
  (continuousOn_univ.mp analyticOnNhd_sourceHilbertMass.continuousOn).comp
    (continuous_subtype_val.comp (continuous_originalWeightedRealSource _))

theorem continuous_fourthClassicalMomentum : Continuous fourthClassicalMomentum :=
  continuous_periodOneSobolevMomentum.comp (nativeSobolevH1PairCLM 4 (by omega)).continuous

/-- The complete physical velocity as continuous spatial functions, with
the initial mass and the actual current momentum on general real pairs. -/
def fourthClassicalVelocity (a b : FourthClassicalSource) : C(AddCircle (2:ℝ),ℂ) × C(AddCircle (2:ℝ),ℂ) :=
  let J0 := nativeSobolevPhysicalJetCLM 4 0 (by omega) b
  let J1 := nativeSobolevPhysicalJetCLM 4 1 (by omega) b
  let J3 := nativeSobolevPhysicalJetCLM 4 3 (by omega) b
  let M := fourthClassicalMass a
  let P := fourthClassicalMomentum b
  (-J3.1+(6:ℂ) • (J0.1*J0.2*J1.1)+(6*P*I) • J0.1-(6*M) • J1.1,
   -J3.2+(6:ℂ) • (J0.1*J0.2*J1.2)-(6*P*I) • J0.2-(6*M) • J1.2)

private theorem continuous_corrected_polynomial {E B : Type*} [TopologicalSpace E]
    [NormedRing B] [NormedAlgebra ℂ B]
    (J0 J1 J3 : E → B × B) (M P : E → ℂ)
    (h0 : Continuous J0) (h1 : Continuous J1) (h3 : Continuous J3)
    (hM : Continuous M) (hP : Continuous P) :
    Continuous (fun z =>
      (-(J3 z).1+(6:ℂ) • ((J0 z).1*(J0 z).2*(J1 z).1)+(6*P z*I) • (J0 z).1-(6*M z) • (J1 z).1,
       -(J3 z).2+(6:ℂ) • ((J0 z).1*(J0 z).2*(J1 z).2)-(6*P z*I) • (J0 z).2-(6*M z) • (J1 z).2)) :=
  (((h3.fst.neg.add (continuous_const.smul ((h0.fst.mul h0.snd).mul h1.fst))).add
    (((continuous_const.mul hP).mul continuous_const).smul h0.fst)).sub
      ((continuous_const.mul hM).smul h1.fst)).prodMk
    (((h3.snd.neg.add (continuous_const.smul ((h0.fst.mul h0.snd).mul h1.snd))).sub
      (((continuous_const.mul hP).mul continuous_const).smul h0.snd)).sub
        ((continuous_const.mul hM).smul h1.snd))

theorem continuous_fourthClassicalVelocity :
    Continuous (fun z : FourthClassicalSource × FourthClassicalSource => fourthClassicalVelocity z.1 z.2) := by
  let J0 := fun z : FourthClassicalSource × FourthClassicalSource => nativeSobolevPhysicalJetCLM 4 0 (by omega) z.2
  let J1 := fun z : FourthClassicalSource × FourthClassicalSource => nativeSobolevPhysicalJetCLM 4 1 (by omega) z.2
  let J3 := fun z : FourthClassicalSource × FourthClassicalSource => nativeSobolevPhysicalJetCLM 4 3 (by omega) z.2
  exact continuous_corrected_polynomial J0 J1 J3
    (fun z => fourthClassicalMass z.1) (fun z => fourthClassicalMomentum z.2)
    ((nativeSobolevPhysicalJetCLM 4 0 (by omega)).continuous.comp continuous_snd)
    ((nativeSobolevPhysicalJetCLM 4 1 (by omega)).continuous.comp continuous_snd)
    ((nativeSobolevPhysicalJetCLM 4 3 (by omega)).continuous.comp continuous_snd)
    (continuous_fourthClassicalMass.comp continuous_fst)
    (continuous_fourthClassicalMomentum.comp continuous_snd)

/-- On every real H⁴ source the bounded-jet formula is exactly the actual
classical corrected differential field, not only a finite-gap formula. -/
theorem fourthClassicalVelocity_eq_classical (a b : FourthClassicalSource) (x : ℝ) :
    let f := fun y : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega) b).1 (y : AddCircle (2:ℝ))
    let g := fun y : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega) b).2 (y : AddCircle (2:ℝ))
    (fourthClassicalVelocity a b).1 (x : AddCircle (2:ℝ)) =
      (classicalCorrectedFourthField (fourthClassicalMass a) (fourthClassicalMomentum b) f g).1 x ∧
    (fourthClassicalVelocity a b).2 (x : AddCircle (2:ℝ)) =
      (classicalCorrectedFourthField (fourthClassicalMass a) (fourthClassicalMomentum b) f g).2 x := by
  dsimp only
  have h1 := iteratedDeriv_nativeSobolevPhysicalJet 4 1 (by omega) b
  have h3 := iteratedDeriv_nativeSobolevPhysicalJet 4 3 (by omega) b
  simp only [iteratedDeriv_succ,iteratedDeriv_zero] at h1 h3
  constructor
  · change _ = (classicalRenormalizedFourthField _ _ _).1 x+6*fourthClassicalMomentum b*I*_
    simp only [classicalRenormalizedFourthField,classicalNLSFourthVectorField_formula,Pi.sub_apply]
    rw [h3.1,h1.1]
    simp only [fourthClassicalVelocity,ContinuousMap.add_apply,ContinuousMap.sub_apply,
      ContinuousMap.neg_apply,ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
    ring
  · change _ = (classicalRenormalizedFourthField _ _ _).2 x-6*fourthClassicalMomentum b*I*_
    simp only [classicalRenormalizedFourthField,classicalNLSFourthVectorField_formula,Pi.sub_apply]
    rw [h3.2,h1.2]
    simp only [fourthClassicalVelocity,ContinuousMap.add_apply,ContinuousMap.sub_apply,
      ContinuousMap.neg_apply,ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
    ring

end NLS.Articles.MKdVBelowL2
