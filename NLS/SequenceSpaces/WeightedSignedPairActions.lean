import NLS.SequenceSpaces.WeightedScalarActionFamilyDescent
import NLS.SequenceSpaces.SignedHilbertPairs

/-! # Exact normalized signed actions and their original weighted norm -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

def signedPairActions (w : Weight) (e : ℤ ≃ ℕ+) (b : DeletedCoeff 2 0) : WeightedCoeff w 1 :=
  actionsFromNormalizedCoordinates w (deletedToSignedPair e b)

theorem signedPairActions_apply (w : Weight) (e : ℤ ≃ ℕ+) (b : DeletedCoeff 2 0) (k : ℤ) :
    (signedPairActions w e b).val k=
      b.val (positiveIndexInjection e k)*b.val (-positiveIndexInjection e k)/(w k : ℂ) := by
  rw [signedPairActions,actionsFromNormalizedCoordinates_apply,
    (deletedToSignedPair_apply e b k).1,(deletedToSignedPair_apply e b k).2]
  have hs : (Real.sqrt 2 : ℂ)^2=2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ)≤2))
  rw [div_pow,div_pow,mul_pow,I_sq,hs]
  ring

theorem analyticOnNhd_signedPairActions (w : Weight) (e : ℤ ≃ ℕ+) :
    AnalyticOnNhd ℂ (signedPairActions w e) univ := by
  intro b _
  exact ((weightIsometry w 1).symm.toContinuousLinearEquiv.analyticAt _).comp
    ((analyticOnNhd_quadraticActionsExponent _ (mem_univ _)).comp ((deletedToSignedPair e).analyticAt b))

theorem signedPairActions_nonnegative (w : Weight) (e : ℤ ≃ ℕ+)
    (b : DeletedCoeff 2 0) (hb : deletedL2Conjugation b=b) :
    signedPairActions w e b∈nonnegativeLocus w 1 := by
  apply (mem_nonnegativeLocus_iff w 1 _).mpr
  change weightIsometry w 1 (actionsFromNormalizedCoordinates w (deletedToSignedPair e b))∈_
  rw [weight_actionsFromNormalizedCoordinates]
  exact Coeff.quadraticActions_mem_nonnegativeLocus _ (deletedToSignedPair_real e b hb)

end NLS.WeightedCoeff
