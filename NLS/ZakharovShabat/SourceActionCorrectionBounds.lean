import NLS.ZakharovShabat.SourceActionFrequencyAsymptotic

/-! # Common source neighborhoods for all refined correction bounds

This property retains the quantifier order needed when descending the
source estimates to action space: choose the neighborhood first, then
choose a norm bound for each admissible target exponent.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Near each real source, every refined target has a bound on the same
open source neighborhood. The scalar correction is fixed before the target. -/
def HasLocallyUniformActionCorrectionBounds (A : SourceAbelianMomentAtlas hp hp1 W s) : Prop :=
  ∀ φ : realTypeSourceSubmodule p, ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧
    ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
        (∀ n, b n = A.actionFrequencyCorrection ψ n) ∧ ‖b‖ ≤ C

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
