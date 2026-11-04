import NLS.Articles.MKdVBelowL2.OrdinaryFourthClassicalTimeEquation

/-! # The ordinary mKdV PDE on the full native real H⁴ diagonal

The restored source flow preserves the original equal fields. Its physical
momentum vanishes on that diagonal, giving the unrenormalized scalar PDE.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier
open scoped ComplexConjugate
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

theorem ordinaryFourthClassicalSourceFlow_diagonal (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (time : ℝ) :
    (originalWeightedRealSource _ (ordinaryFourthClassicalSourceFlow a time)).val.fst =
      (originalWeightedRealSource _ (ordinaryFourthClassicalSourceFlow a time)).val.snd := by
  rw [originalWeightedRealSource_ordinaryFourthClassicalSourceFlow]
  exact ordinaryFourthHilbertImageFlow_preserves_diagonal _ ha time

/-- The actual two physical functions agree on the full H⁴ diagonal. -/
theorem ordinaryFourthClassicalPhysicalValue_diagonal (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (time x : ℝ) :
    (ordinaryFourthClassicalPhysicalValue a time x).1 = (ordinaryFourthClassicalPhysicalValue a time x).2 := by
  have he := nativeSobolevH1PairCLM_diagonal 4 (by omega) (ordinaryFourthClassicalSourceFlow a time)
    (ordinaryFourthClassicalSourceFlow_diagonal a ha time)
  have hs := nativeSobolevPhysicalJet_zero_eq_synthesis 4 (by omega) (ordinaryFourthClassicalSourceFlow a time) x
  exact hs.1.trans ((congrArg (fun q : ScalarDomain 2 => periodOneSobolevSynthesis q (x : AddCircle (2:ℝ))) he).trans hs.2.symm)

/-- The actual physical pair has its original conjugate reality relation. -/
theorem ordinaryFourthClassicalPhysicalValue_real (a : FourthClassicalSource) (time x : ℝ) :
    (ordinaryFourthClassicalPhysicalValue a time x).2 = conj ((ordinaryFourthClassicalPhysicalValue a time x).1) := by
  let b := ordinaryFourthClassicalSourceFlow a time
  let q := nativeSobolevH1PairCLM 4 (by omega) b
  have hr := periodOneSobolevSynthesis_real (⟨q,nativeSobolevH1PairCLM_real 4 (by omega) b⟩ : realTypeSobolevSourceLocus) x
  have hs := nativeSobolevPhysicalJet_zero_eq_synthesis 4 (by omega) b x
  exact hs.2.trans (hr.trans (congrArg conj hs.1.symm))

theorem ordinaryFourthClassicalPhysicalValue_im_eq_zero (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (time x : ℝ) :
    ((ordinaryFourthClassicalPhysicalValue a time x).1).im = 0 := by
  have h := congrArg Complex.im
    ((ordinaryFourthClassicalPhysicalValue_real a time x).symm.trans (ordinaryFourthClassicalPhysicalValue_diagonal a ha time x).symm)
  simp only [Complex.conj_im] at h
  linarith

/-- The independently defined physical H2 vanishes along this actual scalar flow. -/
theorem ordinaryFourthClassicalMomentum_flow_diagonal (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (time : ℝ) :
    fourthClassicalMomentum (ordinaryFourthClassicalSourceFlow a time) = 0 := by
  have he := nativeSobolevH1PairCLM_diagonal 4 (by omega) (ordinaryFourthClassicalSourceFlow a time)
    (ordinaryFourthClassicalSourceFlow_diagonal a ha time)
  change periodOneSobolevMomentum (nativeSobolevH1PairCLM 4 (by omega) (ordinaryFourthClassicalSourceFlow a time)) = 0
  let q := nativeSobolevH1PairCLM 4 (by omega) (ordinaryFourthClassicalSourceFlow a time)
  have hq : q = (q.1,q.1) := Prod.ext rfl he.symm
  change periodOneSobolevMomentum q = 0
  rw [hq]
  exact periodOneSobolevMomentum_diagonal _

/-- Every actual H⁴ scalar datum, with no finite-gap condition, evolves by
the scalar ordinary mKdV PDE at every real time and spatial point. -/
theorem hasDerivAt_ordinaryFourthClassicalPhysicalValue_mKdV (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (time x : ℝ) :
    let u := fun r y => (ordinaryFourthClassicalPhysicalValue a r y).1
    HasDerivAt (fun r => u r x)
      (-deriv (deriv (deriv (u time))) x+6*((u time x)^2-(0:ℂ))*deriv (u time) x) time := by
  dsimp only
  have ht : HasDerivAt (fun r => (ordinaryFourthClassicalPhysicalValue a r x).1)
      (ordinaryFourthClassicalPhysicalVelocity a time x).1 time :=
    (hasDerivAt_ordinaryFourthClassicalPhysicalValue a time x).fst
  have hv := (fourthClassicalVelocity_eq_classical 0 (ordinaryFourthClassicalSourceFlow a time) x).1
  have hd : (fun y : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega)
      (ordinaryFourthClassicalSourceFlow a time)).2 (y : AddCircle (2:ℝ))) =
      (fun y : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega)
        (ordinaryFourthClassicalSourceFlow a time)).1 (y : AddCircle (2:ℝ))) := by
    funext y
    exact (ordinaryFourthClassicalPhysicalValue_diagonal a ha time y).symm
  rw [fourthClassicalMass_zero] at hv
  rw [hd,ordinaryFourthClassicalMomentum_flow_diagonal a ha time] at hv
  simp only [classicalCorrectedFourthField,mul_zero,zero_mul,Pi.add_apply,add_zero] at hv
  rw [classicalRenormalizedFourthField_diagonal] at hv
  change (ordinaryFourthClassicalPhysicalVelocity a time x).1 = _ at hv
  rw [hv] at ht
  exact ht

end NLS.Articles.MKdVBelowL2
