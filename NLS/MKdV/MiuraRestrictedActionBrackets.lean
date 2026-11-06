import NLS.MKdV.MiuraGardnerTransfer
import NLS.ZakharovShabat.SourceDiscriminantPoisson

/-! # Restricted NLS actions commute with the actual mKdV actions

The proved Gardner transfer and original NLS action commutation give the
invariance used for Theorem 4(ii). All signed NLS indices are allowed,
including the central action, and neither selected action must be open.
The remaining factorization through mKdV action coordinates is separate.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraRestrictedNLSAction (m : ℤ) : Coeff 2 → ℂ :=
  sourceComplexAction (by simp) (by norm_num) m ∘ scalarL2Diagonal

theorem miuraRestrictedNLSAction_eq_original (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℤ) :
    miuraRestrictedNLSAction m (scalarInclusion a) = miuraNLSAction a m := by
  change sourceComplexAction (by simp) (by norm_num) m (scalarL2Diagonal (scalarInclusion a)) = _
  rw [scalarL2Diagonal_scalarInclusion]
  change sourceComplexAction (by simp) (by norm_num) m (realDiagonalH1Source a ha).val = _
  rw [sourceComplexAction_eq_sourceRealAction _ _ m _ (realDiagonalH1Source a ha).property]
  exact (sourceIndexedAction_eq_sourceRealAction _ _ m _ (realDiagonalH1Source a ha).property).symm

theorem miuraRestrictedNLSAction_gardner_commutes (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℤ) (n : ℕ) (hn : 1 ≤ n) :
    l2GardnerBracket (miuraRestrictedNLSAction m) (miuraL2Action n) (scalarInclusion a) = 0 := by
  let ψ := realDiagonalH1Source a ha
  have hf : DifferentiableAt ℂ (sourceComplexAction (by simp) (by norm_num) m)
      (scalarL2Diagonal (scalarInclusion a)) := by
    rw [scalarL2Diagonal_scalarInclusion]
    exact (analyticAt_sourceComplexAction_of_realType _ _ m ψ.val ψ.property).differentiableAt
  have hd := hf.hasFDerivAt.comp (scalarInclusion a) scalarL2Diagonal.hasFDerivAt
  change HasFDerivAt (miuraRestrictedNLSAction m) _ _ at hd
  rw [l2GardnerBracket,hd.fderiv,scalarL2Diagonal_scalarInclusion,miuraGardner_cotangent_transfer a ha n hn]
  change sourceBracket le_rfl (sourceComplexAction (by simp) (by norm_num) m)
      (sourceComplexAction (by simp) (by norm_num) n) ψ.val-
    sourceBracket le_rfl (sourceComplexAction (by simp) (by norm_num) m)
      (sourceComplexAction (by simp) (by norm_num) (-(n : ℤ))) ψ.val = 0
  rw [sourceBracket_actions_eq_zero _ _ le_rfl ψ.val ψ.property,
    sourceBracket_actions_eq_zero _ _ le_rfl ψ.val ψ.property,sub_self]

end NLS.MKdV
