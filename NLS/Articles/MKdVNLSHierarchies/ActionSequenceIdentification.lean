import NLS.MKdV.MiuraActionSequenceTopology
import NLS.MKdV.MiuraActionFlowInvariants

/-! # The full physical mKdV action sequence and its native norm

This supplies the infinite action-space map required by the remaining
normal-form assertions. Every coordinate is the independent physical
Hill action on the original real H1 domain. The forward factorization
and independent global mKdV Birkhoff chart remain separate obligations.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem theorem4_mkdv_action_mean_map_analytic :
    ∃ U : Set (ScalarDomain 2), IsOpen U ∧ {a | ∀ j, a.val j = conj (a.val (-j))} ⊆ U ∧
      AnalyticOnNhd ℂ miuraH1ActionMeanMap U ∧
      (∀ (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))),
        (∀ n : ℕ, 1 ≤ n → (miuraH1ActionMeanMap a).1.val (n : ℤ) = miuraMKdVAction a ha n) ∧
        (miuraH1ActionMeanMap a).2 = a.val 0) := by
  obtain ⟨U,hU,hreal,hA⟩ := exists_miuraH1ActionMeanMap_domain
  exact ⟨U,hU,hreal,hA,fun a ha => ⟨fun n hn => miuraH1ActionSequence_physical a ha n hn,rfl⟩⟩

theorem theorem4_weighted_action_summability (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    Summable (fun n : ℕ => (1+((n : ℝ)+1))^3*‖miuraMKdVAction a ha (n+1)‖) :=
  summable_weighted_physical_miuraActions a ha

theorem native_mkdv_action_sequence_analytic (s : ℕ) :
    ∃ U : Set (ScalarSobolev s), IsOpen U ∧
      {a | ∀ j, a.val j = conj (a.val (-j))} ⊆ U ∧
      AnalyticOnNhd ℂ (miuraSobolevActionSequence s) U ∧
      ∀ b ∈ U, ∀ n : ℤ, 0 < n → (miuraSobolevActionSequence s b).val n =
        (1/2 : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (miuraSobolevActionSource s b) :=
  exists_miuraSobolevActionSequence_domain s

theorem native_mkdv_action_sequence_paper_topology (s : ℕ) :
    ∃ U : Set (ScalarSobolev s), IsOpen U ∧
      {a | ∀ j, a.val j = conj (a.val (-j))} ⊆ U ∧
      AnalyticOnNhd ℂ (miuraPaperSobolevActionSequence s) U ∧
      ∀ b ∈ U, ∀ n : ℤ, 0 < n → (miuraPaperSobolevActionSequence s b).val n =
        (1/2 : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (miuraSobolevActionSource s b) :=
  exists_miuraPaperSobolevActionSequence_domain s

theorem theorem4_action_mean_sequence_conserved (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    miuraH1ActionMeanMap (miuraH1ActionFlow a ha n t) = miuraH1ActionMeanMap a := by
  apply Prod.ext
  · apply Subtype.ext
    funext j
    by_cases hj : 0 < j
    · have he : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj.le
      have hn : 1 ≤ j.toNat := by omega
      change (miuraH1ActionSequence (miuraH1ActionFlow a ha n t)).val j = (miuraH1ActionSequence a).val j
      rw [← he,miuraH1ActionSequence_physical _ (miuraH1ActionFlow_real a ha n t) _ hn,
        miuraH1ActionSequence_physical a ha _ hn]
      exact miuraMKdVAction_miuraActionFlow a ha n j.toNat hn t
    · change (miuraH1ActionSequence (miuraH1ActionFlow a ha n t)).val j = (miuraH1ActionSequence a).val j
      rw [miuraH1ActionSequence_nonpositive _ j hj,miuraH1ActionSequence_nonpositive _ j hj]
  · exact miuraActionFlow_mean a ha n t

end NLS.Articles.MKdVNLSHierarchies
