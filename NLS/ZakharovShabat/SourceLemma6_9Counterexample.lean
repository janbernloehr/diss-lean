import NLS.ZakharovShabat.SourceLemma6_9
import NLS.ZakharovShabat.SourcePeriodTwoDisplacementCounterexample

/-!
# Lemma 6.9's printed displacement budget is incompatible with its counted roots

The original spectral counterexample also refutes this bound for any choice
of the counted scalar root pairs. The defect is locally uniform at zero;
the corrected bound in `sourceLemma6_9` retains an additive leading tail.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- No choice of the actual counted determinant roots repairs the printed Hilbert sum bound. -/
theorem not_sourceLemma6_9_printed_pair_sum :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∃ U : Set (CoeffPair 2), IsOpen U ∧ 0 ∈ U ∧
      ∀ φ ∈ U, ∃ ξ η : ℤ → ℂ,
        (∀ n : ℤ, M ≤ n.natAbs → 2 ≤ n.natAbs →
          SourceResonantRootPair (by norm_num) φ n (ξ n) (η n)) ∧
        ∀ N : ℕ, M ≤ N → 2 ≤ N → Summable (rootDisplacementPowerTail 2 N ξ η) ∧
          (∑' n : ℤ, rootDisplacementPowerTail 2 N ξ η n) ≤
            sourcePrintedHilbertDisplacementBudget C φ N := by
  rintro ⟨C,hC,M,U,ho,h0,hbound⟩
  apply not_sourceProposition6_1_printed_pair_sum
  refine ⟨C,hC,M,U,ho,h0,?_⟩
  intro φ hφ
  obtain ⟨ξ,η,hr,ht⟩ := hbound φ hφ
  refine ⟨ξ,η,?_,ht⟩
  intro n hn hn2 z hz hspec
  exact ((hr n (by simpa using hn) (by simpa using hn2)).spectrum_iff z
    (refinedResonantDisk_subset_strip n hz)).mp hspec

end NLS.ZakharovShabat
