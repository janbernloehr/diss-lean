import NLS.SequenceSpaces.BoundedMatrixLimitPointwise

/-!
# Passing operator norm bounds through basis-entry limits

An already bounded limit operator inherits an eventual norm bound
from scalar convergence of its basis entries. Density first supplies
coordinatewise convergence on every input; lower semicontinuity then
retains the original bound.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem opNorm_le_of_basis_limit
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {α : Type*} (l : Filter α) [NeBot l]
    (T : α → Coeff p →L[ℂ] Coeff p) (Q : Coeff p →L[ℂ] Coeff p)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ᶠ i in l, ‖T i‖ ≤ M)
    (hentry : ∀ m k : ℤ,
      Tendsto (fun i => (T i (lp.single p k 1)) m) l
        (𝓝 ((Q (lp.single p k 1)) m))) : ‖Q‖ ≤ M := by
  have hpoint := tendsto_operator_coordinate_of_basis hp l T Q
    (max M ‖Q‖) (le_max_of_le_left hM) (le_max_right _ _)
    (hbound.mono fun i hi => hi.trans (le_max_left _ _)) hentry
  exact opNorm_le_of_coordinatewise_limit l T Q M hM hbound hpoint

end NLS.Coeff
