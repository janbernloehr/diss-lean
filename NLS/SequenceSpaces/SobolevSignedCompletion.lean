import NLS.SequenceSpaces.SignedCompletionLocalAnalytic
import NLS.SequenceSpaces.PeriodOneSobolevMiuraInverse
import NLS.SequenceSpaces.SobolevHalfWeights

/-! # Exact native Sobolev target lifts of signed coordinates

Source conjugation commutes with the literal rough inclusion. Symmetric
weights retain the signed completion coefficients; the half-order target
shift is EXACT, including the original period-one normalization.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.WeightedCoeff

/-- The signed normalized coefficients in their literal native target. -/
def signedTargetLift (v w : Weight) (F : WeightedCoeff v 2 → Coeff 2)
    (q : WeightedCoeff v 2) : WeightedCoeff w 2 :=
  (weightIsometry w 2).symm (normalizedSignedCompletion v F q)

/-- This is the SAME established signed completion, not a replacement
coordinate formula. -/
theorem signedTargetLift_eq_weightedSourceSignedCompletion (v w : Weight)
    (F : WeightedCoeff v 2 → Coeff 2) (q : WeightedCoeff v 2) :
    signedTargetLift v w F q=weightedSourceSignedCompletion v w
      (fun p => (weightIsometry w 2).symm (F p)) q := by
  symm
  simpa only [signedTargetLift,LinearIsometryEquiv.apply_symm_apply] using
    weightedSourceSignedCompletion_eq_normalized v w (fun p => (weightIsometry w 2).symm (F p)) q

@[simp] theorem signedTargetLift_apply (v w : Weight) (F : WeightedCoeff v 2 → Coeff 2)
    (q : WeightedCoeff v 2) (n : ℤ) :
    (signedTargetLift v w F q).val n=normalizedSignedCompletion v F q n/(w n : ℂ) := rfl

/-- Target isometry transport preserves local COMPLEX signed analyticity. -/
theorem analyticOnNhd_signedTargetLift (v w : Weight) (hv : ∀ j, v (-j)=v j)
    (F : WeightedCoeff v 2 → Coeff 2) (U : Set (WeightedCoeff v 2))
    (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (signedTargetLift v w F) (U∩conjugateReflection v hv ⁻¹' U) := by
  intro q hq
  exact ((weightIsometry w 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
    (analyticAt_normalizedSignedCompletion v hv F q (hF q hq.1) (hF _ hq.2))

/-- The actual native target norm is the normalized Hilbert norm. -/
theorem norm_signedTargetLift (v w : Weight) (F : WeightedCoeff v 2 → Coeff 2)
    (q : WeightedCoeff v 2) : ‖signedTargetLift v w F q‖=‖normalizedSignedCompletion v F q‖ :=
  (weightIsometry w 2).symm.norm_map _

end NLS.WeightedCoeff
namespace NLS

/-- Native Sobolev source conjugation and the ACTUAL rough inclusion
commute with EXACT raw coefficients. -/
theorem periodOneSobolevImageInclusion_conjugateReflection
    (t : ℝ) (ht : 0≤t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2) :
    periodOneSobolevImageInclusion t ht
      (WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)) q)=
        periodOneHminusConjugation (periodOneSobolevImageInclusion t ht q) := by
  apply Subtype.ext
  funext n
  rw [periodOneSobolevImageInclusion_apply,WeightedCoeff.conjugateReflection_apply,
    periodOneHminusConjugation_apply,periodOneSobolevImageInclusion_apply]

/-- Every actual real native source is fixed by its native conjugation. -/
theorem sobolev_conjugateReflection_fixed_of_real_inclusion
    (t : ℝ) (ht : 0≤t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hr : ∀ k : ℤ, (periodOneSobolevImageInclusion t ht q).val (-k)=
      conj ((periodOneSobolevImageInclusion t ht q).val k)) :
    WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)) q=q := by
  apply Subtype.ext
  funext n
  have H := congrArg (fun a : PeriodOneHminusOne => a.val n)
    ((periodOneHminusConjugation_fixed_iff _).mpr hr)
  simpa only [WeightedCoeff.conjugateReflection_apply,periodOneHminusConjugation_apply,
    periodOneSobolevImageInclusion_apply] using H

/-- Exact weighted positive values give the SAME signed normalized
values at EVERY complex source where both conjugate germs are available. -/
theorem normalizedSignedCompletion_sobolev_apply
    (t : ℝ) (ht : 0≤t) (P : PeriodOneHminusOne → Coeff 2)
    (F : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hF : ∀ n : ℤ, F q n=(Weight.sobolev t n : ℂ)*P (periodOneSobolevImageInclusion t ht q) n)
    (hFJ : ∀ n : ℤ,
      F (WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)) q) n=
        (Weight.sobolev t n : ℂ)*P (periodOneHminusConjugation (periodOneSobolevImageInclusion t ht q)) n)
    (n : ℤ) :
    WeightedCoeff.normalizedSignedCompletion (Weight.sobolev (t-1)) F q n=
      (Weight.sobolev t n : ℂ)*WeightedCoeff.normalizedSignedCompletion (Weight.sobolev (-1)) P
        (periodOneSobolevImageInclusion t ht q) n := by
  rw [WeightedCoeff.normalizedSignedCompletion_apply _ (Weight.sobolev_neg (t-1)),
    WeightedCoeff.normalizedSignedCompletion_apply _ (Weight.sobolev_neg (-1)),hF n,hFJ (-n)]
  simp only [Weight.sobolev_neg,map_mul,conj_ofReal,periodOneHminusConjugation]
  ring

/-- The full native h^(t-1/2) target includes to the SAME actual rough
h^(-1/2) map; the half-order normalization cancels EXACTLY. -/
theorem signedTargetLift_sobolev_inclusion
    (t : ℝ) (ht : 0≤t) (P : PeriodOneHminusOne → Coeff 2)
    (F : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (he : ∀ n : ℤ, WeightedCoeff.normalizedSignedCompletion (Weight.sobolev (t-1)) F q n=
      (Weight.sobolev t n : ℂ)*WeightedCoeff.normalizedSignedCompletion (Weight.sobolev (-1)) P
        (periodOneSobolevImageInclusion t ht q) n) :
    WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2)
      (WeightedCoeff.signedTargetLift (Weight.sobolev (t-1)) (Weight.sobolev (t-1/2)) F q)=
        WeightedCoeff.signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2)) P
          (periodOneSobolevImageInclusion t ht q) := by
  apply Subtype.ext
  funext n
  rw [WeightedCoeff.sobolevInclusion_apply,WeightedCoeff.signedTargetLift_apply,
    WeightedCoeff.signedTargetLift_apply,he n]
  have hw : (Weight.sobolev (t-1/2) n : ℂ)=
      (Weight.sobolev t n : ℂ)*(Weight.sobolev (-1/2) n : ℂ) := by
    rw [show t-1/2=t+(-1/2) by ring,Weight.sobolev_add,ofReal_mul]
  rw [hw,←div_div,mul_div_cancel_left₀ _ (Weight.complex_ne_zero (Weight.sobolev t) n)]

end NLS
