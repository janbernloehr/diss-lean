import NLS.MKdV.MiuraActionDescent
import NLS.MKdV.MiuraMeanSquareDescent

/-! # The converse action clause of Theorem 4(ii)

The physical mKdV actions are real analytic functions of the original
NLS actions on the full original real H1 domain, without excluding closed
gaps or zero mean. The printed signed-mean assertion is corrected to the
mean squared, with an analytic factor even at zero mean. Signed recovery
still requires a sign-branch restriction.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- The converse `J_n` assertion, with an actual ℓ¹ NLS action map and
open complex action neighborhoods supporting analytic factors. -/
theorem theorem4_ii_mkdv_actions_of_nls_actions :
    ∃ I : CoeffPair 2 → Coeff 1, ∃ U : Set (CoeffPair 2),
      IsOpen U ∧ realTypeSourceLocus 2 ⊆ U ∧ AnalyticOnNhd ℂ I U ∧
      (∀ ψ ∈ U, ∀ m : ℤ, I ψ m = sourceComplexAction (by simp) (by norm_num) m ψ) ∧
      (∀ (a : ScalarDomain 2) (_ha : ∀ j, a.val j = conj (a.val (-j))),
        ∀ m : ℤ, I (sobolevSourceInclusion (a,a)) m = miuraNLSAction a m) ∧
      ∀ (n : ℕ), 1 ≤ n → ∃ V : Set (Coeff 1), ∃ G : Coeff 1 → ℂ,
        IsOpen V ∧ (∀ ψ ∈ realDiagonalSourceLocus 2, I ψ ∈ V) ∧
          AnalyticOnNhd ℂ G V ∧ AnalyticOnNhd ℝ G V ∧
          ∀ (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))),
            G (I (sobolevSourceInclusion (a,a))) = miuraMKdVAction a ha n := by
  obtain ⟨I,U,hU,hreal,hI,hcoords,horiginal,h⟩ := exists_miuraActionLevel_action_extensions
  refine ⟨I,U,hU,hreal,hI,hcoords,horiginal,?_⟩
  intro n hn
  obtain ⟨V,G,hV,hcenters,hG,hGr,hrec⟩ := h n hn 1
  exact ⟨V,G,hV,hcenters,hG,hGr,fun a ha => (hrec a ha).trans (miuraMKdVActionLevel_one a ha n)⟩

/-- Sign-invariant correction of the printed converse mean assertion.
The mean squared is analytic in the NLS actions even at zero mean. -/
theorem theorem4_ii_mean_square_of_nls_actions :
    ∃ I : CoeffPair 2 → Coeff 1, ∃ U : Set (CoeffPair 2),
      IsOpen U ∧ realTypeSourceLocus 2 ⊆ U ∧ AnalyticOnNhd ℂ I U ∧
      (∀ ψ ∈ U, ∀ m : ℤ, I ψ m = sourceComplexAction (by simp) (by norm_num) m ψ) ∧
      (∀ (a : ScalarDomain 2) (_ha : ∀ j, a.val j = conj (a.val (-j))),
        ∀ m : ℤ, I (sobolevSourceInclusion (a,a)) m = miuraNLSAction a m) ∧
      ∃ V : Set (Coeff 1), ∃ G : Coeff 1 → ℂ,
        IsOpen V ∧ (∀ ψ ∈ realDiagonalSourceLocus 2, I ψ ∈ V) ∧
          AnalyticOnNhd ℂ G V ∧ AnalyticOnNhd ℝ G V ∧
          ∀ (a : ScalarDomain 2) (_ha : ∀ j, a.val j = conj (a.val (-j))),
            G (I (sobolevSourceInclusion (a,a))) = (a.val 0)^2 :=
  exists_miuraMeanSquare_action_extension

end NLS.Articles.MKdVNLSHierarchies
