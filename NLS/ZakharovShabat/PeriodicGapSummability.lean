import NLS.ZakharovShabat.PeriodicRootSequence

/-!
# Intrinsic weighted periodic gap power sums

The original contour-defined squared gap eliminates root ordering entirely.
Its norm to the power p/2 is the p-th power of the gap modulus, even when
roots coincide. The corrected quantitative estimate therefore holds for an
intrinsic spectral sequence, locally uniformly for every larger cutoff.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Squaring a complex gap and halving its real power preserves its modulus power. -/
theorem norm_sq_rpow_half (z : ℂ) (P : ℝ) : ‖z^2‖^(P/2) = ‖z‖^P := by
  rw [norm_pow, ← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted power tail of the intrinsic original periodic squared gap. -/
def periodicGapPowerTail (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then (w (2*n))^p.toReal *
    ‖periodicSquaredGap hp (weightedBaseToPair w φ) n‖^(p.toReal/2) else 0

/-- Any pair representing the intrinsic squared gap has exactly the intrinsic weighted power tail. -/
theorem periodicGapPowerTail_eq_rootGapPowerTail (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (h : ∀ n : ℤ, N ≤ n.natAbs → periodicSquaredGap hp (weightedBaseToPair w φ) n = (ξ n-η n)^2) :
    periodicGapPowerTail hp w φ N = rootGapPowerTail p w N ξ η := by
  funext n
  rw [rootGapPowerTail_eq]
  unfold periodicGapPowerTail
  by_cases hn : N ≤ n.natAbs
  · simp only [if_pos hn, h n hn, norm_sq_rpow_half]
  · simp only [if_neg hn]

/-- Corrected Proposition 6.3 in terms of the original intrinsic spectral gap, independent of labels. -/
theorem exists_uniform_periodicGapSummability (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Summable (periodicGapPowerTail hp w ψ N) ∧
        (∑' n : ℤ, periodicGapPowerTail hp w ψ N n) ≤ rootGapBudget w ψ N := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,hroots⟩ := exists_uniform_periodicRoots_with_power_sums hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ N hN
  obtain ⟨ξ,η,hpair,htail⟩ := hroots ψ hψ
  rw [periodicGapPowerTail_eq_rootGapPowerTail hp w ψ N ξ η
    (fun n hn => (hpair n (hN.trans hn)).squaredGap_eq)]
  exact (htail N hN).2.2

end NLS.ZakharovShabat
