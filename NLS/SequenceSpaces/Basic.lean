import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.Basic

/-!
# Sequence spaces for the dNLS formalization

The scalar coefficient space is mathlib's `lp`, indexed by integers.
This module is the starting point for Fourier truncations and weighted spaces.
-/

open scoped ENNReal
noncomputable section

namespace NLS

/-- Complex Fourier coefficients indexed by the integers. -/
abbrev Coeff (p : ℝ≥0∞) := lp (fun _ : ℤ => ℂ) p

end NLS
