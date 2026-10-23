import NLS.ZakharovShabat.SourcePeriodTwoDisplacementCounterexample

/-! # The literal positive-index displacement tail in Proposition 6.1

The printed sum on page 35 ranges over n >= N. The earlier full signed
tail implies the corrected positive-index estimate. Its counterexample
occurs at a positive index and also refutes the literal one-sided sum.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The exact positive-index range of the printed sum, extended by zero to integers. -/
def sourcePositiveDisplacementPowerTail (p : ℝ≥0∞) (N : ℕ) (ξ η : ℤ → ℂ) (n : ℤ) : ℝ :=
  if (N : ℤ) ≤ n then
    ‖ξ n-(Real.pi : ℂ)*n‖^p.toReal + ‖η n-(Real.pi : ℂ)*n‖^p.toReal else 0

theorem sourcePositiveDisplacementPowerTail_nonneg (p : ℝ≥0∞) (N : ℕ)
    (ξ η : ℤ → ℂ) (n : ℤ) : 0 ≤ sourcePositiveDisplacementPowerTail p N ξ η n := by
  unfold sourcePositiveDisplacementPowerTail
  split_ifs <;> positivity

/-- The literal one-sided summand is dominated by the full signed summand. -/
theorem sourcePositiveDisplacementPowerTail_le (p : ℝ≥0∞) (N : ℕ)
    (ξ η : ℤ → ℂ) (n : ℤ) :
    sourcePositiveDisplacementPowerTail p N ξ η n ≤ rootDisplacementPowerTail p N ξ η n := by
  unfold sourcePositiveDisplacementPowerTail rootDisplacementPowerTail
  split_ifs with h hn
  · exact le_rfl
  · have hN : N ≤ n.natAbs := by omega
    exact False.elim (hn hN)
  · positivity
  · exact le_rfl

theorem summable_sourcePositiveDisplacementPowerTail (p : ℝ≥0∞) (N : ℕ)
    (ξ η : ℤ → ℂ) (h : Summable (rootDisplacementPowerTail p N ξ η)) :
    Summable (sourcePositiveDisplacementPowerTail p N ξ η) :=
  Summable.of_nonneg_of_le (sourcePositiveDisplacementPowerTail_nonneg p N ξ η)
    (sourcePositiveDisplacementPowerTail_le p N ξ η) h

theorem tsum_sourcePositiveDisplacementPowerTail_le (p : ℝ≥0∞) (N : ℕ)
    (ξ η : ℤ → ℂ) (h : Summable (rootDisplacementPowerTail p N ξ η)) :
    (∑' n : ℤ, sourcePositiveDisplacementPowerTail p N ξ η n) ≤
      ∑' n : ℤ, rootDisplacementPowerTail p N ξ η n :=
  (summable_sourcePositiveDisplacementPowerTail p N ξ η h).tsum_le_tsum
    (sourcePositiveDisplacementPowerTail_le p N ξ η) h

/-- The corrected estimate also holds on the exact printed positive-index range. -/
theorem exists_uniform_sourcePositiveDisplacement {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs →
            PeriodicResonantPair hp SpectralWeight.one (unitWeightedPairEquiv ψ) n (ξ n) (η n)) ∧
          (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z ∈ resonantStrip n,
            z ∉ sourceResolventSet hp ψ ↔ z = ξ n ∨ z = η n) ∧
          ∀ N : ℕ, N₀ ≤ N → Summable (sourcePositiveDisplacementPowerTail p N ξ η) ∧
            (∑' n : ℤ, sourcePositiveDisplacementPowerTail p N ξ η n) ≤
              sourcePeriodTwoDisplacementBudget ψ N := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,h⟩ := exists_uniform_sourcePeriodTwoDisplacement hp hp1 φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hr,hs,ht⟩ := h ψ hψ
  refine ⟨ξ,η,hr,hs,?_⟩
  intro K hK
  exact ⟨summable_sourcePositiveDisplacementPowerTail p K ξ η (ht K hK).1,
    (tsum_sourcePositiveDisplacementPowerTail_le p K ξ η (ht K hK).1).trans (ht K hK).2⟩

/-- A positive-index spectral witness is controlled by the literal printed pair sum. -/
theorem sourcePeriodTwoRoot_sq_le_positive_pair_tail (N n : ℕ) (hn : N ≤ n)
    (ξ η : ℤ → ℂ) (z : ℂ) (hz : z = ξ n ∨ z = η n)
    (hs : Summable (sourcePositiveDisplacementPowerTail 2 N ξ η)) :
    ‖z-(Real.pi : ℂ)*(n : ℤ)‖^2 ≤
      ∑' k : ℤ, sourcePositiveDisplacementPowerTail 2 N ξ η k := by
  have hterm := hs.le_tsum (n : ℤ)
    (fun k _ => sourcePositiveDisplacementPowerTail_nonneg 2 N ξ η k)
  have he : sourcePositiveDisplacementPowerTail 2 N ξ η (n : ℤ) =
      ‖ξ n-(Real.pi : ℂ)*(n : ℤ)‖^2 + ‖η n-(Real.pi : ℂ)*(n : ℤ)‖^2 := by
    simp [sourcePositiveDisplacementPowerTail, hn]
  rw [he] at hterm
  rcases hz with rfl | rfl
  · exact (le_add_of_nonneg_right (sq_nonneg _)).trans hterm
  · exact (le_add_of_nonneg_left (sq_nonneg _)).trans hterm

/-- The locally uniform printed estimate fails for its literal positive-index pair sum. -/
theorem not_sourceProposition6_1_printed_positive_pair_sum :
    ¬∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ, ∃ U : Set (CoeffPair 2), IsOpen U ∧ 0 ∈ U ∧
      ∀ φ ∈ U, ∃ ξ η : ℤ → ℂ,
        (∀ n : ℕ, M ≤ n → 2 ≤ n → ∀ z ∈ refinedResonantDisk (n : ℤ),
          z ∉ sourceResolventSet (by norm_num) φ → z = ξ n ∨ z = η n) ∧
        ∀ N : ℕ, M ≤ N → 2 ≤ N → Summable (sourcePositiveDisplacementPowerTail 2 N ξ η) ∧
          (∑' n : ℤ, sourcePositiveDisplacementPowerTail 2 N ξ η n) ≤
            sourcePrintedHilbertDisplacementBudget C φ N := by
  rintro ⟨C,hC,M,U,ho,h0,hbound⟩
  obtain ⟨n,hn,hn2,φ,hφ,z,hz,hspec,hbad⟩ :=
    exists_sourcePeriodTwoRoot_exceeding_printed_budget C hC U ho h0 M
  obtain ⟨ξ,η,hr,ht⟩ := hbound φ hφ
  have hb := sourcePeriodTwoRoot_sq_le_positive_pair_tail n n le_rfl ξ η z
    (hr n hn hn2 z hz hspec) (ht n hn hn2).1
  exact (not_le_of_gt hbad) (hb.trans (ht n hn hn2).2)

end NLS.ZakharovShabat
