import NLS.ZakharovShabat.SourceWeightedGapCounterexample

/-! # The literal positive-index gap tail in Proposition 6.3

The printed page-36 sum uses n >= N. Nonnegative domination transfers the
corrected bound; the existing actual positive gap witness refutes the
printed budget on precisely this range.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The intrinsic weighted gap power on the exact printed positive-index range. -/
def sourcePositiveGapPowerTail (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) : ℝ :=
  if (N : ℤ) ≤ n then (w (2*n))^p.toReal *
    ‖periodicSquaredGap hp (weightedBaseToPair w φ) n‖^(p.toReal/2) else 0

theorem sourcePositiveGapPowerTail_nonneg (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) :
    0 ≤ sourcePositiveGapPowerTail hp w φ N n := by
  unfold sourcePositiveGapPowerTail
  split_ifs
  · exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (w.one_le _)) _)
      (Real.rpow_nonneg (norm_nonneg _) _)
  · exact le_rfl

/-- The one-sided intrinsic gap tail is dominated by the full signed tail. -/
theorem sourcePositiveGapPowerTail_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) :
    sourcePositiveGapPowerTail hp w φ N n ≤ periodicGapPowerTail hp w φ N n := by
  unfold sourcePositiveGapPowerTail periodicGapPowerTail
  split_ifs with h hn
  · exact le_rfl
  · have hN : N ≤ n.natAbs := by omega
    exact False.elim (hn hN)
  · exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (w.one_le _)) _)
      (Real.rpow_nonneg (norm_nonneg _) _)
  · exact le_rfl

theorem summable_sourcePositiveGapPowerTail (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (hs : Summable (periodicGapPowerTail hp w φ N)) :
    Summable (sourcePositiveGapPowerTail hp w φ N) :=
  Summable.of_nonneg_of_le (sourcePositiveGapPowerTail_nonneg hp w φ N)
    (sourcePositiveGapPowerTail_le hp w φ N) hs

theorem tsum_sourcePositiveGapPowerTail_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (hs : Summable (periodicGapPowerTail hp w φ N)) :
    (∑' n : ℤ, sourcePositiveGapPowerTail hp w φ N n) ≤
      ∑' n : ℤ, periodicGapPowerTail hp w φ N n :=
  (summable_sourcePositiveGapPowerTail hp w φ N hs).tsum_le_tsum
    (sourcePositiveGapPowerTail_le hp w φ N) hs

/-- Corrected Proposition 6.3 on its printed range, retaining actual source spectra. -/
theorem sourceProposition6_3_corrected_positive (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N₀ ≤ n.natAbs → PeriodicResonantPair hp w ψ n (ξ n) (η n)) ∧
          (∀ n : ℤ, N₀ ≤ n.natAbs → ∀ z ∈ resonantStrip n,
            z ∉ sourceResolventSet hp (sourceWeightedPeriodTwoInput w ψ) ↔ z = ξ n ∨ z = η n) ∧
          ∀ N : ℕ, N₀ ≤ N → Summable (sourcePositiveGapPowerTail hp w ψ N) ∧
            (∑' n : ℤ, sourcePositiveGapPowerTail hp w ψ N n) ≤ rootGapBudget w ψ N := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := sourceProposition6_3_corrected hp hp1 w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hpair,hspec,ht⟩ := hr ψ hψ
  refine ⟨ξ,η,hpair,hspec,?_⟩
  intro K hK
  exact ⟨summable_sourcePositiveGapPowerTail hp w ψ K (ht K hK).1,
    (tsum_sourcePositiveGapPowerTail_le hp w ψ K (ht K hK).1).trans (ht K hK).2⟩

/-- The literal one-sided printed gap sum fails locally uniformly at p=2, unit weight. -/
theorem not_sourceProposition6_3_printed_positive_gap_sum :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ,
      ∃ U : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2), IsOpen U ∧ 0 ∈ U ∧
        ∀ φ ∈ U, ∀ N : ℕ, M ≤ N → 2 ≤ N →
          Summable (sourcePositiveGapPowerTail (by norm_num) SpectralWeight.one φ N) ∧
          (∑' n : ℤ, sourcePositiveGapPowerTail (by norm_num) SpectralWeight.one φ N n) ≤
            sourcePrintedHilbertGapBudget C SpectralWeight.one φ N := by
  rintro ⟨C,hC,M,U,ho,h0,hbound⟩
  obtain ⟨n,hn,hn2,φ,hφ,hbad⟩ :=
    exists_periodicGap_exceeding_printed_ceiling_budget C hC U ho h0 M
  obtain ⟨hs,hb⟩ := hbound φ hφ n hn hn2
  have hterm := hs.le_tsum (n : ℤ)
    (fun k _ => sourcePositiveGapPowerTail_nonneg (by norm_num) SpectralWeight.one φ n k)
  have hle : ‖periodicSquaredGap (by norm_num) (weightedBaseToPair SpectralWeight.one φ) n‖ ≤
      ∑' k : ℤ, sourcePositiveGapPowerTail (by norm_num) SpectralWeight.one φ n k := by
    simpa [sourcePositiveGapPowerTail] using hterm
  exact (not_le_of_gt hbad) (hle.trans hb)

/-- The corresponding labeled weighted gap on the printed positive-index range. -/
def sourcePositiveRootGapPowerTail (p : ℝ≥0∞) (w : SpectralWeight)
    (N : ℕ) (ξ η : ℤ → ℂ) (n : ℤ) : ℝ :=
  if (N : ℤ) ≤ n then (w (2*n)*‖ξ n-η n‖)^p.toReal else 0

/-- Actual counted pairs represent the intrinsic tail independently of their order. -/
theorem sourcePositiveGapPowerTail_eq_rootGap (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (h : ∀ n : ℤ, (N : ℤ) ≤ n →
      periodicSquaredGap hp (weightedBaseToPair w φ) n = (ξ n-η n)^2) :
    sourcePositiveGapPowerTail hp w φ N = sourcePositiveRootGapPowerTail p w N ξ η := by
  funext n
  unfold sourcePositiveGapPowerTail sourcePositiveRootGapPowerTail
  split_ifs with hn
  · rw [h n hn, norm_sq_rpow_half, Real.mul_rpow (zero_le_one.trans (w.one_le _)) (norm_nonneg _)]
  · rfl

/-- No choice of actual counted high pairs satisfies the literal weighted gap estimate. -/
theorem not_sourceProposition6_3_printed_positive_pair_sum :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∃ M : ℕ,
      ∃ U : Set (WeightedCoeffPair SpectralWeight.one.toWeight 2), IsOpen U ∧ 0 ∈ U ∧
        ∀ φ ∈ U, ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, (M : ℤ) ≤ n → (2 : ℤ) ≤ n →
            PeriodicResonantPair (by norm_num) SpectralWeight.one φ n (ξ n) (η n)) ∧
          ∀ N : ℕ, M ≤ N → 2 ≤ N →
            Summable (sourcePositiveRootGapPowerTail 2 SpectralWeight.one N ξ η) ∧
            (∑' n : ℤ, sourcePositiveRootGapPowerTail 2 SpectralWeight.one N ξ η n) ≤
              sourcePrintedHilbertGapBudget C SpectralWeight.one φ N := by
  rintro ⟨C,hC,M,U,ho,h0,hr⟩
  apply not_sourceProposition6_3_printed_positive_gap_sum
  refine ⟨C,hC,M,U,ho,h0,?_⟩
  intro φ hφ N hN hN2
  obtain ⟨ξ,η,hpair,ht⟩ := hr φ hφ
  rw [sourcePositiveGapPowerTail_eq_rootGap (by norm_num) SpectralWeight.one φ N ξ η
    (fun n hn => (hpair n (by omega) (by omega)).squaredGap_eq)]
  exact ht N hN hN2

end NLS.ZakharovShabat
