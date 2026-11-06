import NLS.SequenceSpaces.SignedCompletionDerivative
import NLS.SequenceSpaces.SignedReciprocalSymbol

/-! # Literal multiplier form of the full signed native principal -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.WeightedCoeff

/-- The actual reflected derivative of a multiplier uses the reflected
CONJUGATE symbol whenever the actual free map preserves the real form. -/
theorem reflectedDerivative_multiplier
    (v : Weight) (hv : ∀ n, v (-n)=v n)
    (Q : WeightedCoeff v 2 →L[ℂ] Coeff 2)
    (hQ : ∀ h, Q (conjugateReflection v hv h)=periodOneL2Conjugation (Q h))
    (a : Coeff ⊤) :
    reflectedDerivative v hv ((Coeff.holderProduct (q := 2) a).comp Q)=
      (Coeff.holderProduct (q := 2) (Coeff.symbolConjugation a)).comp Q := by
  ext h n
  change conj (a (-n)*Q (conjugateReflection v hv h) (-n))=conj (a (-n))*Q h n
  rw [hQ,periodOneL2Conjugation_apply,map_mul,neg_neg,conj_conj]

/-- Both exact native signed terms combine to the literal full signed
symbol, followed by the SAME real-compatible free map and target inverse. -/
theorem nativeSignedPrincipal_multiplier
    (v w : Weight) (hv : ∀ n, v (-n)=v n)
    (Q : WeightedCoeff v 2 →L[ℂ] Coeff 2)
    (hQ : ∀ h, Q (conjugateReflection v hv h)=periodOneL2Conjugation (Q h))
    (a : Coeff ⊤) :
    nativeSignedPrincipal v w hv ((Coeff.holderProduct (q := 2) a).comp Q)
      ((Coeff.holderProduct (q := 2) a).comp Q)=
      (weightIsometry w 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((Coeff.holderProduct (q := 2) (Coeff.completedPositiveSymbol a)).comp Q) := by
  unfold nativeSignedPrincipal
  rw [reflectedDerivative_multiplier v hv Q hQ a]
  congr 1
  ext h n
  change a n*Q h n+Coeff.symbolConjugation a n*Q h n=Coeff.completedPositiveSymbol a n*Q h n
  rw [Coeff.completedPositiveSymbol_apply,Coeff.symbolConjugation_apply]
  ring

end NLS.WeightedCoeff
