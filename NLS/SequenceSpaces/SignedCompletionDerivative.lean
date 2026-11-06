import NLS.SequenceSpaces.SobolevSignedCompletion
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Exact derivative and compact remainders of signed completion

Source and target conjugate reflection are actual bounded antilinear
maps. Their double composition gives a complex-linear derivative.
Compact remainders survive both conjugations, on genuine complex germs.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.WeightedCoeff

/-- The actual native conjugate reflection as a bounded antilinear map. -/
def conjugateReflectionSLM (v : Weight) (hv : ∀ j, v (-j)=v j) :
    WeightedCoeff v 2 →SL[starRingEnd ℂ] WeightedCoeff v 2 :=
  ({ toFun := conjugateReflection v hv
     map_add' := by
      intro a b
      apply Subtype.ext
      funext n
      simp only [conjugateReflection_apply,add_val,map_add]
     map_smul' := by
      intro c a
      apply Subtype.ext
      funext n
      simp only [conjugateReflection_apply,smul_val,map_mul] } :
    WeightedCoeff v 2 →ₛₗ[starRingEnd ℂ] WeightedCoeff v 2).mkContinuous 1
    (by
      intro a
      change ‖conjugateReflection v hv a‖≤1*‖a‖
      rw [norm_conjugateReflection,one_mul])

@[simp] theorem conjugateReflectionSLM_apply (v : Weight) (hv : ∀ j, v (-j)=v j)
    (a : WeightedCoeff v 2) : conjugateReflectionSLM v hv a=conjugateReflection v hv a := rfl

/-- Conjugating the source and target of a positive derivative preserves
complex linearity and retains literal physical reflection at both ends. -/
def reflectedDerivative (v : Weight) (hv : ∀ j, v (-j)=v j)
    (A : WeightedCoeff v 2 →L[ℂ] Coeff 2) : WeightedCoeff v 2 →L[ℂ] Coeff 2 :=
  ((starL ℂ : Coeff 2 ≃L⋆[ℂ] Coeff 2).toContinuousLinearMap.comp
    (Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap).comp
      (A.comp (conjugateReflectionSLM v hv))

@[simp] theorem reflectedDerivative_apply (v : Weight) (hv : ∀ j, v (-j)=v j)
    (A : WeightedCoeff v 2 →L[ℂ] Coeff 2) (h : WeightedCoeff v 2) :
    reflectedDerivative v hv A h=periodOneL2Conjugation (A (conjugateReflection v hv h)) := rfl

/-- Both conjugations preserve actual compactness. -/
theorem isCompactOperator_reflectedDerivative (v : Weight) (hv : ∀ j, v (-j)=v j)
    (A : WeightedCoeff v 2 →L[ℂ] Coeff 2) (hA : IsCompactOperator A) :
    IsCompactOperator (reflectedDerivative v hv A) :=
  (hA.comp_clm (conjugateReflectionSLM v hv)).clm_comp
    ((starL ℂ : Coeff 2 ≃L⋆[ℂ] Coeff 2).toContinuousLinearMap.comp
      (Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The exact signed derivative uses both actual conjugate source germs. -/
theorem hasFDerivAt_normalizedSignedCompletion (v : Weight) (hv : ∀ j, v (-j)=v j)
    (F : WeightedCoeff v 2 → Coeff 2) (q : WeightedCoeff v 2)
    (A B : WeightedCoeff v 2 →L[ℂ] Coeff 2)
    (hA : HasFDerivAt F A q) (hB : HasFDerivAt F B (conjugateReflection v hv q)) :
    HasFDerivAt (normalizedSignedCompletion v F) (A+reflectedDerivative v hv B) q := by
  have H := HasFDerivAt.comp_semilinear
    ((starL ℂ : Coeff 2 ≃L⋆[ℂ] Coeff 2).toContinuousLinearMap.comp
      (Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap)
    (conjugateReflectionSLM v hv) (z := q) hB
  have he : normalizedSignedCompletion v F=
      fun p => F p+periodOneL2Conjugation (F (conjugateReflection v hv p)) := by
    funext p
    rw [normalizedSignedCompletion_eq v hv]
    ext n
    simp only [lp.coeFn_add,Pi.add_apply,Coeff.reflection_apply,lp.star_apply,
      periodOneL2Conjugation_apply,starRingEnd_apply]
  rw [he]
  exact hA.add H

/-- A compact positive remainder at BOTH actual conjugate source points
gives a compact remainder of the FULL complex signed derivative. -/
theorem isCompactOperator_signedDerivative_sub (v : Weight) (hv : ∀ j, v (-j)=v j)
    (F : WeightedCoeff v 2 → Coeff 2) (q : WeightedCoeff v 2)
    (hF : DifferentiableAt ℂ F q) (hFJ : DifferentiableAt ℂ F (conjugateReflection v hv q))
    (A B : WeightedCoeff v 2 →L[ℂ] Coeff 2)
    (hA : IsCompactOperator (fderiv ℂ F q-A))
    (hB : IsCompactOperator (fderiv ℂ F (conjugateReflection v hv q)-B)) :
    IsCompactOperator (fderiv ℂ (normalizedSignedCompletion v F) q-
      (A+reflectedDerivative v hv B)) := by
  rw [(hasFDerivAt_normalizedSignedCompletion v hv F q _ _ hF.hasFDerivAt hFJ.hasFDerivAt).fderiv]
  have he : (fderiv ℂ F q+reflectedDerivative v hv (fderiv ℂ F (conjugateReflection v hv q)))-
      (A+reflectedDerivative v hv B)=
      (fderiv ℂ F q-A)+reflectedDerivative v hv (fderiv ℂ F (conjugateReflection v hv q)-B) := by
    ext h n
    simp only [_root_.add_apply,_root_.sub_apply,reflectedDerivative_apply,
      periodOneL2Conjugation_apply,lp.coeFn_add,Pi.add_apply,lp.coeFn_sub,Pi.sub_apply,map_sub]
    ring
  rw [he]
  exact hA.add (isCompactOperator_reflectedDerivative v hv _ hB)

/-- The literal native full signed principal operator after target-weight
transport. Both positive and reflected principal terms are retained. -/
def nativeSignedPrincipal (v w : Weight) (hv : ∀ j, v (-j)=v j)
    (A B : WeightedCoeff v 2 →L[ℂ] Coeff 2) :
    WeightedCoeff v 2 →L[ℂ] WeightedCoeff w 2 :=
  (weightIsometry w 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A+reflectedDerivative v hv B)

/-- The full native target transport preserves the compact remainder
of the actual complex signed derivative, including its half-order weight. -/
theorem isCompactOperator_fderiv_signedTargetLift_sub
    (v w : Weight) (hv : ∀ j, v (-j)=v j)
    (F : WeightedCoeff v 2 → Coeff 2) (q : WeightedCoeff v 2)
    (hF : DifferentiableAt ℂ F q) (hFJ : DifferentiableAt ℂ F (conjugateReflection v hv q))
    (A B : WeightedCoeff v 2 →L[ℂ] Coeff 2)
    (hA : IsCompactOperator (fderiv ℂ F q-A))
    (hB : IsCompactOperator (fderiv ℂ F (conjugateReflection v hv q)-B)) :
    IsCompactOperator (fderiv ℂ (signedTargetLift v w F) q-nativeSignedPrincipal v w hv A B) := by
  let I := (weightIsometry w 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hd := I.hasFDerivAt.comp q
    (hasFDerivAt_normalizedSignedCompletion v hv F q _ _ hF.hasFDerivAt hFJ.hasFDerivAt)
  have hder : fderiv ℂ (signedTargetLift v w F) q=
      I.comp (fderiv ℂ (normalizedSignedCompletion v F) q) := by
    change fderiv ℂ (I ∘ normalizedSignedCompletion v F) q=_
    rw [hd.fderiv,(hasFDerivAt_normalizedSignedCompletion v hv F q _ _ hF.hasFDerivAt hFJ.hasFDerivAt).fderiv]
  rw [hder]
  have he : I.comp (fderiv ℂ (normalizedSignedCompletion v F) q)-nativeSignedPrincipal v w hv A B=
      I.comp (fderiv ℂ (normalizedSignedCompletion v F) q-(A+reflectedDerivative v hv B)) := by
    apply ContinuousLinearMap.ext
    intro h
    exact (I.map_sub _ _).symm
  rw [he]
  exact (isCompactOperator_signedDerivative_sub v hv F q hF hFJ A B hA hB).clm_comp I

end NLS.WeightedCoeff
