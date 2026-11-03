import NLS.MKdV.MiuraLocalNLSActionFactor

/-! # Local forward action factorization with the signed mean

Near the free profile the full restricted original NLS action sequence is
an analytic function of the native physical mKdV actions and signed mean.
The same common factor applies on the literal original real H1 domain,
where every positive input action is the independent Hill-contour action.
The global forward clause of Theorem 4(ii) remains an essential obligation.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- Local forward factorization in the original L2 topology, simultaneously
for every original signed NLS action, with no nonzero-mean assumption. -/
theorem original_NLS_actions_local_analytic_physical_action_mean_factor :
    ∃ U : Set (Coeff 2), ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen U ∧ (0 : Coeff 2) ∈ U ∧ IsOpen V ∧ (0 : MiuraActionMeanTarget) ∈ V ∧
      AnalyticOnNhd ℂ F V ∧
      ∀ a ∈ U, (∀ j, a j = conj (a (-j))) →
        miuraL2ActionMeanMap a ∈ V ∧ ∀ k : ℤ,
          F (miuraL2ActionMeanMap a) k =
            sourceComplexAction (by simp) (by norm_num) k (scalarL2Diagonal a) := by
  obtain ⟨U,V,F,hU,h0U,hV,h0V,hF,he⟩ := exists_local_miura_original_NLS_action_factor
  refine ⟨U,V,F,hU,h0U,hV,h0V,hF,?_⟩
  intro a ha har
  obtain ⟨hmem,hrec⟩ := he a ha har
  refine ⟨hmem,fun k => ?_⟩
  rw [hrec]
  exact miuraOriginalNLSActionSequence_apply a (real_mem_miuraOriginalNLSActionDomain a har) k

/-- Every positive input coordinate is the independent original-H1
physical Hill action, including at a closed selected gap. -/
theorem local_factor_input_original_H1_action (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    (miuraL2ActionMeanMap (scalarInclusion a)).1.val (n : ℤ) = miuraMKdVAction a ha n := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraL2ActionSequence_domain
  exact (hcoord _ (hreal har) n hn).trans (miuraL2Action_eq_physical a ha n hn)

/-- Original-H1 recovery for any local original-L2 action factor. -/
theorem original_H1_recovery_of_L2_factor
    (U : Set (Coeff 2)) (V : Set MiuraActionMeanTarget) (F : MiuraActionMeanTarget → Coeff 1)
    (he : ∀ a ∈ U, (∀ j, a j = conj (a (-j))) →
      miuraL2ActionMeanMap a ∈ V ∧ ∀ k : ℤ,
        F (miuraL2ActionMeanMap a) k = sourceComplexAction (by simp) (by norm_num) k (scalarL2Diagonal a))
    (a : ScalarDomain 2) (ha : scalarInclusion a ∈ U) (har : ∀ j, a.val j = conj (a.val (-j))) :
    miuraL2ActionMeanMap (scalarInclusion a) ∈ V ∧
    (∀ n : ℕ, 1 ≤ n → (miuraL2ActionMeanMap (scalarInclusion a)).1.val (n : ℤ) = miuraMKdVAction a har n) ∧
    (miuraL2ActionMeanMap (scalarInclusion a)).2 = a.val 0 ∧
    ∀ k : ℤ, F (miuraL2ActionMeanMap (scalarInclusion a)) k =
      sourceComplexAction (by simp) (by norm_num) k (sobolevSourceInclusion (a,a)) := by
  have harL2 : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using har j
  obtain ⟨hmem,hrec⟩ := he (scalarInclusion a) ha harL2
  refine ⟨hmem,fun n hn => local_factor_input_original_H1_action a har n hn,?_,fun k => ?_⟩
  · exact scalarInclusion_apply a 0
  · simpa only [scalarL2Diagonal_scalarInclusion] using hrec k

/-- Original H1 inclusion pulls open original L2 sets back to open sets. -/
theorem isOpen_original_H1_pullback (U : Set (Coeff 2)) (hU : IsOpen U) :
    IsOpen ((scalarInclusion : ScalarDomain 2 →L[ℂ] Coeff 2) ⁻¹' U) :=
  hU.preimage scalarInclusion.continuous

/-- The inclusion preserves the zero base point of a local chart. -/
theorem zero_mem_original_H1_pullback (U : Set (Coeff 2)) (h0U : (0 : Coeff 2) ∈ U) :
    (0 : ScalarDomain 2) ∈ (scalarInclusion : ScalarDomain 2 →L[ℂ] Coeff 2) ⁻¹' U :=
  @NLS.ComplexAnalysis.zero_mem_preimage_clm (ScalarDomain 2) (Coeff 2)
    inferInstance inferInstance inferInstance inferInstance scalarInclusion U h0U

/-- The same analytic factor recovers all original restricted NLS actions
on one original H1 neighborhood, with the physical J_n inputs and signed
mean. The neighborhoods precede both action indices. -/
theorem original_H1_NLS_actions_local_physical_action_mean_factor :
    ∃ U : Set (Coeff 2), ∃ V : Set MiuraActionMeanTarget, ∃ F : MiuraActionMeanTarget → Coeff 1,
      IsOpen U ∧ (0 : Coeff 2) ∈ U ∧ IsOpen V ∧ (0 : MiuraActionMeanTarget) ∈ V ∧
      AnalyticOnNhd ℂ F V ∧
      ∀ a : ScalarDomain 2, scalarInclusion a ∈ U → ∀ ha : ∀ j, a.val j = conj (a.val (-j)),
        miuraL2ActionMeanMap (scalarInclusion a) ∈ V ∧
        (∀ n : ℕ, 1 ≤ n → (miuraL2ActionMeanMap (scalarInclusion a)).1.val (n : ℤ) = miuraMKdVAction a ha n) ∧
        (miuraL2ActionMeanMap (scalarInclusion a)).2 = a.val 0 ∧
        ∀ k : ℤ, F (miuraL2ActionMeanMap (scalarInclusion a)) k =
          sourceComplexAction (by simp) (by norm_num) k (sobolevSourceInclusion (a,a)) := by
  obtain ⟨U,V,F,hU,h0U,hV,h0V,hF,he⟩ := original_NLS_actions_local_analytic_physical_action_mean_factor
  refine ⟨U,V,F,hU,h0U,hV,h0V,hF,?_⟩
  exact original_H1_recovery_of_L2_factor U V F he

end NLS.Articles.MKdVNLSHierarchies
