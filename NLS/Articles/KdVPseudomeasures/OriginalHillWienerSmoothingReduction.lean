import NLS.Articles.KdVPseudomeasures.OriginalHillWienerModels
import NLS.SequenceSpaces.SignedHilbertWienerInclusion
import NLS.FunctionalAnalysis.AnalyticSmoothingRestriction

/-! A precise reduction of the actual Wiener Birkhoff problem to the
one-smoothing defect of the SAME actual integer Hilbert Birkhoff map.
The smoothing statement is an EXPLICIT unproved premise here. Once
supplied, no separate Wiener inverse-regularity premise is needed. -/
noncomputable section
open NLS.KdV NLS.WeightedCoeff NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def HillIntegerNativeOneSmoothing (N : ℕ) : Prop :=
  ∃ R : RealSignedHilbert (signedStepOrder 0 N) →
      RealSignedHilbert (signedStepOrder (1/2) N + 1),
    (∀ q, AnalyticAt ℝ R q) ∧ ∀ q k,
      (R q).val.val.val k = ((hillIntegerSobolevEquiv N).equiv q).val.val.val k -
        halfFourierSymbol k * q.val.val.val k

def HillWienerBirkhoffDiffeomorphism (N : ℕ) : Prop :=
  ∃ e : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1 ≃
      fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) 1,
    (∀ q k, (e q).val.val.val k = (hillRealSignedMap (hillWienerSourceInclusion N q)).val.val.val k) ∧
    (∀ q, AnalyticAt ℝ e q) ∧ (∀ z, AnalyticAt ℝ e.symm z)

theorem hillWienerBirkhoffDiffeomorphism_of_oneSmoothing (N : ℕ)
    (hs : HillIntegerNativeOneSmoothing N) : HillWienerBirkhoffDiffeomorphism N := by
  obtain ⟨R,hR,hcoeff⟩ := hs
  let iE := hillWienerSourceHilbertInclusion N
  let iF := hillWienerTargetHilbertInclusion N
  let A := hillIntegerFreeFourierEquiv N 1
  let A₀ := hillIntegerFreeFourierEquiv N 2
  let S := signedRealHilbertWienerInclusion (signedStepOrder (1/2) N)
  let e := (hillIntegerSobolevEquiv N).equiv
  have hA (q : fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1) :
      iF (A q) = A₀ (iE q) := hillIntegerFreeFourierEquiv_Wiener_compatibility N q
  have hdef (q : RealSignedHilbert (signedStepOrder 0 N)) : e q = A₀ q + iF (S (R q)) := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    change (e q).val.val.val k = (A₀ q).val.val.val k + (iF (S (R q))).val.val.val k
    rw [hillIntegerFreeFourierEquiv_apply, hillWienerTargetHilbertInclusion_apply,
      signedRealHilbertWienerInclusion_apply, hcoeff]
    ring
  obtain ⟨E,hInc,hAn,hInv⟩ := @exists_analytic_smoothingRestrictionEquiv ℝ
    (fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1)
    (fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder (1/2) N)) 1)
    (RealSignedHilbert (signedStepOrder 0 N)) (RealSignedHilbert (signedStepOrder (1/2) N))
    (RealSignedHilbert (signedStepOrder (1/2) N + 1))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance iE iF
    (hillWienerSourceHilbertInclusion_injective N) (hillWienerTargetHilbertInclusion_injective N)
    A A₀ S R e hA hdef hR (hillIntegerSobolevEquiv N).analytic_symm
  refine ⟨E, ?_, ?_, ?_⟩
  · intro q k
    have hc := congrArg (fun z : RealSignedHilbert (signedStepOrder (1/2) N) => z.val.val.val k) (hInc q)
    rw [hillWienerTargetHilbertInclusion_apply] at hc
    rw [← hillIntegerTargetInclusion_apply N, hillIntegerSobolevEquiv_inclusion] at hc
    exact hc
  · exact hAn
  · exact hInv

end NLS.Articles.KdVPseudomeasures
