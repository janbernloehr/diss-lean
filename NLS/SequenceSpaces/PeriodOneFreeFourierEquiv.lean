import NLS.SequenceSpaces.PeriodOneMiuraInverseCompact
import NLS.SequenceSpaces.DeletedRestrictionEquiv
import NLS.SequenceSpaces.PeriodOneMiuraConjugation

/-! # The exact native free Fourier/Miura equivalence and its real form -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS

/-- The actual free Miura inverse followed by the exact native weight. -/
def periodOneNativeFreeFourierEquiv (t : ℝ) (ht : 0≤t) :
    WeightedCoeff (Weight.sobolev (t-1)) 2 ≃L[ℂ] Coeff 2 :=
  (periodOneSobolevFreeMassEquiv 0 t ht).symm.trans
    (WeightedCoeff.weightIsometry (Weight.sobolev t) 2).toContinuousLinearEquiv

theorem periodOneSobolevFreeMassEquiv_symm_apply (t : ℝ) (ht : 0≤t)
    (a : WeightedCoeff (Weight.sobolev (t-1)) 2) (n : ℤ) :
    ((periodOneSobolevFreeMassEquiv 0 t ht).symm a).val n=
      (periodOneMassSymbol 0 n)⁻¹*a.val n := by
  have h := congrArg (fun b : WeightedCoeff (Weight.sobolev (t-1)) 2 => b.val n)
    ((periodOneSobolevFreeMassEquiv 0 t ht).apply_symm_apply a)
  rw [periodOneSobolevFreeMassEquiv_apply,periodOneSobolevMassOperator_apply] at h
  apply (mul_left_cancel₀ (periodOneMassSymbol_ne_zero 0 n))
  rw [←mul_assoc,mul_inv_cancel₀ (periodOneMassSymbol_ne_zero 0 n),one_mul]
  exact h

@[simp] theorem periodOneNativeFreeFourierEquiv_apply (t : ℝ) (ht : 0≤t)
    (a : WeightedCoeff (Weight.sobolev (t-1)) 2) (n : ℤ) :
    periodOneNativeFreeFourierEquiv t ht a n=
      (Weight.sobolev t n : ℂ)*((periodOneMassSymbol 0 n)⁻¹*a.val n) := by
  change (Weight.sobolev t n : ℂ)*((periodOneSobolevFreeMassEquiv 0 t ht).symm a).val n=_
  rw [periodOneSobolevFreeMassEquiv_symm_apply]

/-- The SAME bounded equivalence commutes with actual physical conjugation. -/
theorem periodOneNativeFreeFourierEquiv_conjugation (t : ℝ) (ht : 0≤t)
    (a : WeightedCoeff (Weight.sobolev (t-1)) 2) :
    periodOneNativeFreeFourierEquiv t ht
      (WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)) a)=
      periodOneL2Conjugation (periodOneNativeFreeFourierEquiv t ht a) := by
  ext n
  simp only [periodOneNativeFreeFourierEquiv_apply,WeightedCoeff.conjugateReflection_apply,
    periodOneL2Conjugation_apply,map_mul,map_inv₀,Weight.sobolev_neg]
  change (Weight.sobolev t n : ℂ)*((periodOneMassSymbol 0 n)⁻¹*conj (a.val (-n)))=
    conj (Weight.sobolev t n : ℂ)*((conj (periodOneMassSymbol 0 (-n)))⁻¹*conj (a.val (-n)))
  rw [conj_ofReal,periodOneMassSymbol_conjugation]

/-- The same free equivalence in the literal normalized source chart. -/
def periodOneNormalizedFreeFourierEquiv (t : ℝ) (ht : 0≤t) : Coeff 2 ≃L[ℂ] Coeff 2 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev (t-1)) 2).symm.toContinuousLinearEquiv.trans
    (periodOneNativeFreeFourierEquiv t ht)

@[simp] theorem periodOneNormalizedFreeFourierEquiv_zero (t : ℝ) (ht : 0≤t) (a : Coeff 2) :
    periodOneNormalizedFreeFourierEquiv t ht a 0=a 0 := by
  change periodOneNativeFreeFourierEquiv t ht
    ((WeightedCoeff.weightIsometry (Weight.sobolev (t-1)) 2).symm a) 0=_
  rw [periodOneNativeFreeFourierEquiv_apply]
  change (Weight.sobolev t 0 : ℂ)*((periodOneMassSymbol 0 0)⁻¹*(a 0/(Weight.sobolev (t-1) 0 : ℂ)))=a 0
  simp [periodOneMassSymbol]

/-- Its restriction is an ACTUAL bounded equivalence of the native
mean-zero chart. No new multiplier bound or inverse is postulated. -/
def periodOneMeanZeroFreeFourierEquiv (t : ℝ) (ht : 0≤t) : DeletedCoeff 2 0 ≃L[ℂ] DeletedCoeff 2 0 :=
  Coeff.deletedRestrictionEquiv 0 (periodOneNormalizedFreeFourierEquiv t ht)
    (fun a => by rw [periodOneNormalizedFreeFourierEquiv_zero])

end NLS
