import NLS.MKdV.MiuraGeneralLocalNLSActionFactor
import NLS.Articles.MKdVNLSHierarchies.LocalForwardActionFactorization

/-! # Local forward analytic action factors at every original real H1 point

The source and action neighborhoods precede all action indices. Inputs
are the independently identified physical Hill actions and literal signed
mean, including zero mean and arbitrary collapsed gaps. Gluing these
factors to one ambient complex action domain is a separate assertion.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- Every original physical H1 profile has a common local holomorphic
factor for the entire signed NLS action sequence in native action space. -/
theorem original_NLS_actions_local_action_mean_factor_general_H1 (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∃ U : Set (Coeff 2), ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen U ∧ scalarInclusion a ∈ U ∧ IsOpen V ∧ miuraL2ActionMeanMap (scalarInclusion a) ∈ V ∧
      AnalyticOnNhd ℂ F V ∧ ∀ b ∈ U, (∀ j, b j = conj (b (-j))) →
        miuraL2ActionMeanMap b ∈ V ∧ ∀ k : ℤ,
          F (miuraL2ActionMeanMap b) k = sourceComplexAction (by simp) (by norm_num) k (scalarL2Diagonal b) := by
  obtain ⟨U,V,F,hU,haU,hV,haV,hF,hrec⟩ := exists_local_miura_original_NLS_action_factor_at_H1 a ha
  refine ⟨U,V,F,hU,haU,hV,haV,hF,?_⟩
  intro b hb hbr
  obtain ⟨hmem,he⟩ := hrec b hb hbr
  refine ⟨hmem,fun k => ?_⟩
  rw [he]
  exact miuraOriginalNLSActionSequence_apply b (real_mem_miuraOriginalNLSActionDomain b hbr) k

/-- Original-H1 recovery of all NLS actions through independent physical
Hill actions and the signed mean near every original real H1 basepoint. -/
theorem original_H1_NLS_actions_local_physical_factor_general_H1 (a₀ : ScalarDomain 2)
    (ha₀ : ∀ j, a₀.val j = conj (a₀.val (-j))) :
    ∃ U : Set (Coeff 2), ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen U ∧ scalarInclusion a₀ ∈ U ∧ IsOpen V ∧ miuraL2ActionMeanMap (scalarInclusion a₀) ∈ V ∧
      AnalyticOnNhd ℂ F V ∧
      ∀ a : ScalarDomain 2, scalarInclusion a ∈ U → ∀ ha : ∀ j, a.val j = conj (a.val (-j)),
        miuraL2ActionMeanMap (scalarInclusion a) ∈ V ∧
        (∀ n : ℕ, 1 ≤ n → (miuraL2ActionMeanMap (scalarInclusion a)).1.val (n : ℤ) = miuraMKdVAction a ha n) ∧
        (miuraL2ActionMeanMap (scalarInclusion a)).2 = a.val 0 ∧
        ∀ k : ℤ, F (miuraL2ActionMeanMap (scalarInclusion a)) k =
          sourceComplexAction (by simp) (by norm_num) k (sobolevSourceInclusion (a,a)) := by
  obtain ⟨U,V,F,hU,haU,hV,haV,hF,hrec⟩ := original_NLS_actions_local_action_mean_factor_general_H1 a₀ ha₀
  exact ⟨U,V,F,hU,haU,hV,haV,hF,original_H1_recovery_of_L2_factor U V F hrec⟩

end NLS.Articles.MKdVNLSHierarchies
