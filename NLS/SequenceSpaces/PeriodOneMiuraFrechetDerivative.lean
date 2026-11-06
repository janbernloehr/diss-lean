import NLS.SequenceSpaces.PeriodOneSobolevMiuraInverse
import NLS.SequenceSpaces.PeriodOneMiuraGlobalCompactness
import NLS.SequenceSpaces.PeriodOneRealFormIdentity
import NLS.FunctionalAnalysis.CompactEquivPerturbation

/-! # The literal full unshifted Miura derivative and its Fredholm principal -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

def periodOneMiuraFrechetDerivative (u : Coeff 2) : Coeff 2 →L[ℂ] PeriodOneHminusOne :=
  periodOneMiuraJacobian 0 u-periodOneL2Inclusion

theorem hasFDerivAt_periodOneMiura (u : Coeff 2) :
    HasFDerivAt periodOneMiura (periodOneMiuraFrechetDerivative u) u :=
  (hasFDerivAt_periodOneShiftedMiura 0 u).sub periodOneL2Inclusion.hasFDerivAt

theorem analyticAt_periodOneMiura (u : Coeff 2) : AnalyticAt ℂ periodOneMiura u :=
  (analyticAt_periodOneShiftedMiura 0 u).sub (periodOneL2Inclusion.analyticAt u)

theorem periodOneMiuraFrechetDerivative_apply (u v : Coeff 2) (j : ℤ) :
    (periodOneMiuraFrechetDerivative u v).val j =
      2*I*(Real.pi : ℂ)*j*v j+2*(periodOneMiuraProduct u v).val j := by
  change (periodOneMiuraJacobian 0 u v).val j-(periodOneL2Inclusion v).val j = _
  rw [periodOneMiuraJacobian_apply,periodOneL2Inclusion_apply]
  simp only [periodOneMassSymbol,Nat.cast_zero,zero_add,ofReal_one]
  ring

theorem periodOneMiura_conjugation (u : Coeff 2) :
    periodOneHminusConjugation (periodOneMiura u) = periodOneMiura (periodOneL2Conjugation u) := by
  have hi : periodOneHminusConjugation (periodOneL2Inclusion u) =
      periodOneL2Inclusion (periodOneL2Conjugation u) := by
    apply Subtype.ext
    funext j
    simp only [periodOneHminusConjugation_apply,periodOneL2Inclusion_apply,periodOneL2Conjugation_apply]
  unfold periodOneMiura
  rw [periodOneHminusConjugation_sub,periodOneShiftedMiura_conjugation,hi]

theorem isCompactOperator_periodOneMiuraFrechetDerivative_sub_mass (u : Coeff 2) :
    IsCompactOperator (periodOneMiuraFrechetDerivative u-(periodOneMassEquiv 0).toContinuousLinearMap) := by
  have hp : IsCompactOperator (periodOneMiuraProduct u) :=
    isCompactOperator_boundedCoefficientsHminusOne.comp_clm
      (Coeff.youngConvolutionCLM youngRelation_two_two_top u)
  have he : periodOneMiuraFrechetDerivative u-(periodOneMassEquiv 0).toContinuousLinearMap =
      (2 : ℂ) • periodOneMiuraProduct u-periodOneL2Inclusion := by
    change (periodOneMassOperator 0+(2 : ℂ) • periodOneMiuraProduct u-periodOneL2Inclusion)-
      periodOneMassOperator 0 = _
    abel
  rw [he]
  exact (hp.smul (2 : ℂ)).sub isCompactOperator_periodOneL2Inclusion

/-- Failure of actual bijectivity gives a NONZERO actual kernel vector;
no eigenvector or injectivity failure is assumed as an extra input. -/
theorem exists_periodOneMiura_kernel_of_not_bijective (u : Coeff 2)
    (hn : ¬Function.Bijective (periodOneMiuraFrechetDerivative u)) :
    ∃ v : Coeff 2, v ≠ 0 ∧ periodOneMiuraFrechetDerivative u v = 0 := by
  by_contra h
  have hz (v : Coeff 2) (hv : periodOneMiuraFrechetDerivative u v = 0) : v = 0 := by
    by_contra hv0
    exact h ⟨v,hv0,hv⟩
  have hi : Function.Injective (periodOneMiuraFrechetDerivative u) := by
    intro v w hvw
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,hvw,sub_self]
  exact hn (bijective_of_compact_sub_equiv_of_injective _ (periodOneMassEquiv 0)
    (isCompactOperator_periodOneMiuraFrechetDerivative_sub_mass u) hi)

end NLS
