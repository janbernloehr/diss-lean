import NLS.Dynamics.PhaseAlmostPeriodic
import NLS.SequenceSpaces.WeightedPhaseFlow

/-! # Almost periodicity in weighted coefficient norms

The actual weighted norms and original coefficients are retained throughout.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Weighted diagonal phase orbits are uniformly almost periodic in the native
weighted norm, for every positive weight and every finite exponent. -/
theorem bohrAlmostPeriodic_phaseFlow (w : Weight) (hp : p ≠ ⊤)
    (ω : ℤ → ℝ) (a : WeightedCoeff w p) :
    Dynamics.BohrAlmostPeriodic (fun t : ℝ => phaseFlow w ω t a) := by
  let b := weightIsometry w p a
  have h := (Coeff.bohrAlmostPeriodic_phaseFlow hp ω b).comp_continuousOn_compact
    _ (Coeff.isCompact_dominatedBox hp b)
    (fun t n => (Coeff.norm_phaseMultiply_apply (fun n => t*ω n) b n).le)
    (weightIsometry w p).symm (weightIsometry w p).symm.continuous.continuousOn
  exact h

end NLS.WeightedCoeff
