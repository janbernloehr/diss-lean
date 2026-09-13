import NLS.SequenceSpaces.IteratedRowTesting

/-!
# Domination by the two-index Hölder test
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- A pointwise majorant proves joint convergence and the exact two-index Hölder norm bound. -/
theorem dominated_double_test (a d f : Coeff p) (b c : Coeff q) (m : ℤ) (F : ℤ × ℤ → ℂ)
    (hF : ∀ jk, ‖F jk‖ ≤ ‖d jk.1 * a (m-jk.1-jk.2) * c jk.2 * b jk.1 * f jk.2‖) :
    Summable (fun jk => ‖F jk‖) ∧ ‖∑' jk, F jk‖ ≤ ‖d‖ * ‖f‖ * ‖iteratedConvolutionRow a b c m‖ := by
  have ht := summable_iteratedRowTest_prod a d f b c m
  have hs := ht.of_nonneg_of_le (fun _ => norm_nonneg _) hF
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' jk, ‖F jk‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' jk : ℤ × ℤ, ‖d jk.1 * a (m-jk.1-jk.2) * c jk.2 * b jk.1 * f jk.2‖ := hs.tsum_le_tsum hF ht
    _ = ∑' j : ℤ, ∑' k : ℤ, ‖d j * a (m-j-k) * c k * b j * f k‖ := ht.tsum_prod
    _ ≤ _ := tsum_norm_iteratedRowTest_le a d f b c m

end NLS.Coeff
