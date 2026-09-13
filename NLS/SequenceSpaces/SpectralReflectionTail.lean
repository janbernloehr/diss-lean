import NLS.SequenceSpaces.SpectralReflection
import NLS.SequenceSpaces.WeightedFourierTail

/-!
# Spectral reflection and weighted tails
-/

noncomputable section
open scoped ENNReal
namespace NLS.SpectralWeight
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reflection preserves the exact symmetric cutoff, including boundary coefficients. -/
theorem reflection_fourierTail (w : SpectralWeight) (N : ℕ) (a : WeightedCoeff w.toWeight p) :
    w.reflection (WeightedCoeff.fourierTail w.toWeight N a) =
      WeightedCoeff.fourierTail w.toWeight N (w.reflection a) := by
  apply Subtype.ext
  funext k
  simp only [reflection_apply, WeightedCoeff.fourierTail_apply, Int.natAbs_neg]

/-- The reflected tail retains exactly the original weighted tail norm. -/
theorem norm_fourierTail_reflection (w : SpectralWeight) (N : ℕ) (a : WeightedCoeff w.toWeight p) :
    ‖WeightedCoeff.fourierTail w.toWeight N (w.reflection a)‖ = ‖WeightedCoeff.fourierTail w.toWeight N a‖ := by
  rw [← w.reflection_fourierTail, LinearIsometryEquiv.norm_map]

/-- Weighted scalar tail norms decrease as their integer cutoffs increase. -/
theorem norm_fourierTail_antitone (w : SpectralWeight) (a : WeightedCoeff w.toWeight p) :
    Antitone (fun N => ‖WeightedCoeff.fourierTail w.toWeight N a‖) := by
  intro M N hMN
  dsimp only
  rw [WeightedCoeff.norm_eq w.toWeight p, WeightedCoeff.norm_eq w.toWeight p, WeightedCoeff.weightEquiv_fourierTail,
    WeightedCoeff.weightEquiv_fourierTail]
  exact Coeff.norm_fourierTail_antitone (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' _ hMN

end NLS.SpectralWeight
