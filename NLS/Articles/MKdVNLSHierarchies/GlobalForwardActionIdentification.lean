import NLS.MKdV.MiuraGlobalNLSActionFactor
import NLS.Articles.MKdVNLSHierarchies.ActionDescentIdentification
import NLS.Articles.MKdVNLSHierarchies.LocalForwardActionFactorization

/-! # The global forward clause of Theorem 4(ii)

One common open complex native action/mean domain contains the data of
every original real H1 profile. One holomorphic l1-valued factor recovers
all original signed NLS actions. Inputs are the independent Hill actions
and literal signed mean, including zero mean and arbitrary closed gaps.
Together with ActionDescentIdentification, this proves Theorem 4(ii) with
the printed converse signed mean corrected to mean squared.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem miuraOriginalNLSActionSequence_original_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (k : ℤ) :
    miuraOriginalNLSActionSequence (scalarInclusion a) k = miuraNLSAction a k := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  rw [miuraOriginalNLSActionSequence_apply _ (real_mem_miuraOriginalNLSActionDomain _ har),
    scalarL2Diagonal_scalarInclusion]
  let ψ := realDiagonalH1Source a ha
  change sourceComplexAction (by simp) (by norm_num) k ψ.val =
    sourceIndexedAction (by simp) (by norm_num) k ψ.val
  rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) k ψ.val ψ.property,
    sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) k ψ.val ψ.property]

/-- The global forward assertion of Theorem 4(ii), simultaneously for
all original signed NLS actions. The common open action domain and factor
precede every original real H1 profile and both action indices. -/
theorem theorem4_ii_nls_actions_of_mkdv_actions_mean :
    ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen V ∧
        (∀ a : ScalarDomain 2, (∀ j, a.val j = conj (a.val (-j))) → miuraL2ActionMeanMap (scalarInclusion a) ∈ V) ∧
        AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℝ F V ∧
        ∀ a : ScalarDomain 2, ∀ ha : ∀ j, a.val j = conj (a.val (-j)),
          (∀ n : ℕ, 1 ≤ n → (miuraL2ActionMeanMap (scalarInclusion a)).1.val (n : ℤ) = miuraMKdVAction a ha n) ∧
          (miuraL2ActionMeanMap (scalarInclusion a)).2 = a.val 0 ∧
          ∀ k : ℤ, F (miuraL2ActionMeanMap (scalarInclusion a)) k = miuraNLSAction a k := by
  obtain ⟨V,F,hV,hall,hF,hrec⟩ := exists_global_miura_original_H1_NLS_action_factor
  refine ⟨V,F,hV,hall,hF,hF.restrictScalars,?_⟩
  intro a ha
  refine ⟨fun n hn => local_factor_input_original_H1_action a ha n hn,scalarInclusion_apply a 0,?_⟩
  intro k
  rw [hrec a ha]
  exact miuraOriginalNLSActionSequence_original_H1 a ha k

end NLS.Articles.MKdVNLSHierarchies
