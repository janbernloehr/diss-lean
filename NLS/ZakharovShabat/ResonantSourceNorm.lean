import NLS.ZakharovShabat.ResonantPotentialModes

/-!
# Exact shifted norms of resonant potential sources

The signed shift cancels the Fourier wave in each source vector. Its norm
is exactly the norm of the single potential component, without a pair-norm
factor and without a normalization assumption on the weight at zero.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed shift removes the negative resonant wave from its potential source. -/
theorem pairModulation_source_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    w.pairModulation n (weightedResonantSource hp w φ n 0) =
      (WeightedCoeffPair.toMax w.toWeight p).symm (0, φ.snd) := by
  apply weightedPair_ext <;> intro k
  · change (w.pairModulation n (weightedResonantSource hp w φ n 0)).fst.val k = 0
    simp
  · change (w.modulation n (weightedResonantSource hp w φ n 0).snd).val k = φ.snd.val k
    simp

/-- The signed shift removes the positive resonant wave from its potential source. -/
theorem pairModulation_source_one (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    w.pairModulation n (weightedResonantSource hp w φ n 1) =
      (WeightedCoeffPair.toMax w.toWeight p).symm (φ.fst, 0) := by
  apply weightedPair_ext <;> intro k
  · change (w.modulation (-n) (weightedResonantSource hp w φ n 1).fst).val k = φ.fst.val k
    simp
  · change (w.pairModulation n (weightedResonantSource hp w φ n 1)).snd.val k = 0
    simp

/-- The first source has exactly the weighted norm of the positive potential component. -/
theorem shiftedPairNorm_source_zero (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    w.shiftedPairNorm n (weightedResonantSource hp w φ n 0) = ‖φ.snd‖ := by
  rw [SpectralWeight.shiftedPairNorm, pairModulation_source_zero]
  exact WithLp.norm_toLp_snd p _ _ _

/-- The second source has exactly the weighted norm of the negative potential component. -/
theorem shiftedPairNorm_source_one (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) :
    w.shiftedPairNorm n (weightedResonantSource hp w φ n 1) = ‖φ.fst‖ := by
  rw [SpectralWeight.shiftedPairNorm, pairModulation_source_one]
  exact WithLp.norm_toLp_fst p _ _ _

end NLS.ZakharovShabat
