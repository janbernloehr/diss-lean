import NLS.Articles.MKdVBelowL2.FourthClassicalTimeEquation
import NLS.ZakharovShabat.SourceSobolevEnergyCoercivity
import NLS.ZakharovShabat.PeriodOneSobolevMomentumSymmetry

/-! # The actual physical fourth flow solves scalar mKdV on the full H⁴ diagonal

The pointwise time equation has no finite-gap hypothesis. Actual source
diagonal preservation removes the momentum phase term, and the physical mass
is the original unit-period integral of the initial scalar field squared.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier
open scoped ComplexConjugate
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

theorem fourthClassicalSourceFlow_diagonal (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (time : ℝ) :
    (originalWeightedRealSource _ (fourthClassicalSourceFlow a time)).val.fst =
      (originalWeightedRealSource _ (fourthClassicalSourceFlow a time)).val.snd := by
  rw [originalWeightedRealSource_fourthClassicalSourceFlow]
  exact fourthHilbertImageFlow_preserves_diagonal _ ha time

/-- The actual two physical functions agree on the full H⁴ diagonal. -/
theorem fourthClassicalPhysicalValue_diagonal (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (time x : ℝ) :
    (fourthClassicalPhysicalValue a time x).1 = (fourthClassicalPhysicalValue a time x).2 := by
  have he := nativeSobolevH1PairCLM_diagonal 4 (by omega) (fourthClassicalSourceFlow a time)
    (fourthClassicalSourceFlow_diagonal a ha time)
  have hs := nativeSobolevPhysicalJet_zero_eq_synthesis 4 (by omega) (fourthClassicalSourceFlow a time) x
  exact hs.1.trans ((congrArg (fun q : ScalarDomain 2 => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ))) he).trans hs.2.symm)

/-- The actual physical pair has its original conjugate reality relation. -/
theorem fourthClassicalPhysicalValue_real (a : FourthClassicalSource) (time x : ℝ) :
    (fourthClassicalPhysicalValue a time x).2 = conj ((fourthClassicalPhysicalValue a time x).1) := by
  let b := fourthClassicalSourceFlow a time
  let q := nativeSobolevH1PairCLM 4 (by omega) b
  have hr := periodOneSobolevSynthesis_real (⟨q,nativeSobolevH1PairCLM_real 4 (by omega) b⟩ : realTypeSobolevSourceLocus) x
  have hs := nativeSobolevPhysicalJet_zero_eq_synthesis 4 (by omega) b x
  exact hs.2.trans (hr.trans (congrArg conj hs.1.symm))

theorem fourthClassicalPhysicalValue_im_eq_zero (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (time x : ℝ) :
    ((fourthClassicalPhysicalValue a time x).1).im = 0 := by
  have h := congrArg Complex.im
    ((fourthClassicalPhysicalValue_real a time x).symm.trans (fourthClassicalPhysicalValue_diagonal a ha time x).symm)
  simp only [Complex.conj_im] at h
  linarith

/-- The independently defined physical H2 vanishes along this actual scalar flow. -/
theorem fourthClassicalMomentum_flow_diagonal (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (time : ℝ) :
    fourthClassicalMomentum (fourthClassicalSourceFlow a time) = 0 := by
  have he := nativeSobolevH1PairCLM_diagonal 4 (by omega) (fourthClassicalSourceFlow a time)
    (fourthClassicalSourceFlow_diagonal a ha time)
  change periodOneSobolevMomentum (nativeSobolevH1PairCLM 4 (by omega) (fourthClassicalSourceFlow a time)) = 0
  let q := nativeSobolevH1PairCLM 4 (by omega) (fourthClassicalSourceFlow a time)
  have hq : q = (q.1,q.1) := Prod.ext rfl he.symm
  change periodOneSobolevMomentum q = 0
  rw [hq]
  exact periodOneSobolevMomentum_diagonal _

/-- The mass coefficient is exactly the original integral of the square
of the initial real physical scalar representative on the unit period. -/
theorem fourthClassicalMass_eq_integral_square (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) :
    fourthClassicalMass a = ∫ x in (0:ℝ)..1, ((fourthClassicalPhysicalValue a 0 x).1)^2 := by
  let q := nativeSobolevH1PairCLM 4 (by omega) a
  have hm : periodOneSobolevMass q = fourthClassicalMass a := by
    rw [periodOneSobolevMass_eq_sourceHilbertMass,sobolevSourceInclusion_nativeSobolevH1PairCLM]
    rfl
  rw [← hm,periodOneSobolevMass_eq_integral q.1 q.2]
  apply intervalIntegral.integral_congr
  intro x _
  change periodOneSobolevSynthesis q.1 (x : AddCircle (2:ℝ))*periodOneSobolevSynthesis q.2 (x : AddCircle (2:ℝ)) =
    ((fourthClassicalPhysicalValue a 0 x).1)^2
  have hs := nativeSobolevPhysicalJet_zero_eq_synthesis 4 (by omega) a x
  have h0 : fourthClassicalPhysicalValue a 0 x =
      ((nativeSobolevPhysicalJetCLM 4 0 (by omega) a).1 (x : AddCircle (2:ℝ)),
       (nativeSobolevPhysicalJetCLM 4 0 (by omega) a).2 (x : AddCircle (2:ℝ))) := by
    unfold fourthClassicalPhysicalValue fourthClassicalPhysicalFlow
    rw [fourthClassicalSourceFlow_zero]
  have hd := fourthClassicalPhysicalValue_diagonal a ha 0 x
  rw [h0] at hd ⊢
  rw [← hs.1,← hs.2]
  dsimp only at hd ⊢
  rw [← hd]
  ring

/-- Every actual H⁴ scalar datum, with no finite-gap condition, evolves by
the scalar renormalized mKdV PDE at every real time and spatial point. -/
theorem hasDerivAt_fourthClassicalPhysicalValue_mKdV (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (time x : ℝ) :
    let u := fun r y => (fourthClassicalPhysicalValue a r y).1
    HasDerivAt (fun r => u r x)
      (-deriv (deriv (deriv (u time))) x+6*((u time x)^2-fourthClassicalMass a)*deriv (u time) x) time := by
  dsimp only
  have ht : HasDerivAt (fun r => (fourthClassicalPhysicalValue a r x).1)
      (fourthClassicalPhysicalVelocity a time x).1 time :=
    (hasDerivAt_fourthClassicalPhysicalValue a time x).fst
  have hv := (fourthClassicalVelocity_eq_classical a (fourthClassicalSourceFlow a time) x).1
  have hd : (fun y : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega)
      (fourthClassicalSourceFlow a time)).2 (y : AddCircle (2:ℝ))) =
      (fun y : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega)
        (fourthClassicalSourceFlow a time)).1 (y : AddCircle (2:ℝ))) := by
    funext y
    exact (fourthClassicalPhysicalValue_diagonal a ha time y).symm
  rw [hd,fourthClassicalMomentum_flow_diagonal a ha time] at hv
  simp only [classicalCorrectedFourthField,mul_zero,zero_mul,Pi.add_apply,add_zero] at hv
  rw [classicalRenormalizedFourthField_diagonal] at hv
  change (fourthClassicalPhysicalVelocity a time x).1 = _ at hv
  rw [hv] at ht
  exact ht

end NLS.Articles.MKdVBelowL2
