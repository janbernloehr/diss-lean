import NLS.ZakharovShabat.SourcePositiveDisplacementTail
import NLS.ZakharovShabat.SourceLemma6_9

/-! # Corrected positive-index versions of Lemma 6.9

The two-root positive tail is bounded by the signed tail. Repeating the
first root's term, as on printed page 43, is bounded by twice that tail.
The original determinant, multiplicities, strip control and neighborhood
are preserved in both versions.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Repeating one label costs at most a factor two relative to the signed pair tail. -/
theorem sourcePositiveDisplacementPowerTail_self_le (p : ℝ≥0∞) (N : ℕ)
    (ξ η : ℤ → ℂ) (n : ℤ) :
    sourcePositiveDisplacementPowerTail p N ξ ξ n ≤ 2 * rootDisplacementPowerTail p N ξ η n := by
  unfold sourcePositiveDisplacementPowerTail rootDisplacementPowerTail
  split_ifs with h hn
  · have hnonneg : 0 ≤ ‖η n-(Real.pi : ℂ)*n‖^p.toReal := Real.rpow_nonneg (norm_nonneg _) _
    nlinarith
  · have hN : N ≤ n.natAbs := by omega
    exact False.elim (hn hN)
  · positivity
  · norm_num

/-- Summability and a doubled upper bound hold for the literal repeated-label sum. -/
theorem sourcePositiveDisplacementPowerTail_self_summable_and_le (p : ℝ≥0∞) (N : ℕ)
    (ξ η : ℤ → ℂ) (hs : Summable (rootDisplacementPowerTail p N ξ η)) :
    Summable (sourcePositiveDisplacementPowerTail p N ξ ξ) ∧
      (∑' n : ℤ, sourcePositiveDisplacementPowerTail p N ξ ξ n) ≤
        2 * ∑' n : ℤ, rootDisplacementPowerTail p N ξ η n := by
  have htwo := hs.mul_left 2
  have hs' := Summable.of_nonneg_of_le (sourcePositiveDisplacementPowerTail_nonneg p N ξ ξ)
    (sourcePositiveDisplacementPowerTail_self_le p N ξ η) htwo
  refine ⟨hs',?_⟩
  simpa only [tsum_mul_left] using hs'.tsum_le_tsum (sourcePositiveDisplacementPowerTail_self_le p N ξ η) htwo

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Corrected positive-index sums, including the literal repeated first label, on one source neighborhood. -/
theorem sourceLemma6_9_corrected_positive (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ n : ℤ, N₀ ≤ n.natAbs →
        AnalyticOnNhd ℂ (fun s : CoeffPair p × ℂ => sourceResonantDeterminantFunction hp s.1 n s.2)
          (U ×ˢ resonantStrip n) ∧ ∀ ψ ∈ U, SourceResonantStripControl hp ψ n) ∧
      ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ,
        (∀ n : ℤ, N₀ ≤ n.natAbs → SourceResonantRootPair hp ψ n (ξ n) (η n)) ∧
        ∀ N : ℕ, N₀ ≤ N →
          (Summable (sourcePositiveDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, sourcePositiveDisplacementPowerTail p N ξ η n) ≤ sourcePeriodTwoDisplacementBudget ψ N) ∧
          (Summable (sourcePositiveDisplacementPowerTail p N ξ ξ) ∧
            (∑' n : ℤ, sourcePositiveDisplacementPowerTail p N ξ ξ n) ≤ 2 * sourcePeriodTwoDisplacementBudget ψ N) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hcontrol,hr⟩ := sourceLemma6_9 hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,hcontrol,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hpair,ht⟩ := hr ψ hψ
  refine ⟨ξ,η,hpair,?_⟩
  intro K hK
  have hsum := (ht K hK).1
  have hdup := sourcePositiveDisplacementPowerTail_self_summable_and_le p K ξ η hsum
  exact ⟨⟨summable_sourcePositiveDisplacementPowerTail p K ξ η hsum,
      (tsum_sourcePositiveDisplacementPowerTail_le p K ξ η hsum).trans (ht K hK).2⟩,
    ⟨hdup.1,hdup.2.trans (mul_le_mul_of_nonneg_left (ht K hK).2 (by norm_num))⟩⟩

end NLS.ZakharovShabat
