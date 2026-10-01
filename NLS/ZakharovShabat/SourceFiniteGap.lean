import NLS.ZakharovShabat.SourceBoundaryTerminalDifferential

/-! # Actual finite-gap sources

Finite-gap means only finitely many actual indexed periodic gaps are
open. This is a spectral property, not finite Fourier support. Collapsed
gaps force their terminal anti-discriminants to vanish, so a finite-gap
source has only finitely many nonperiodic Dirichlet terminals.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real sources with only finitely many actual open periodic gaps. -/
def sourceFiniteGapLocus (hp : p ≠ ⊤) (hp1 : 1 < p) : Set (realTypeSourceLocus p) :=
  {φ | {j : ℤ | canonicalPeriodicGap hp hp1
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j ≠ 0}.Finite}

/-- Only finitely many terminal anti-discriminants can be nonzero
at an actual finite-gap source, for every finite exponent above one. -/
theorem finite_nonperiodic_terminals_of_mem_sourceFiniteGapLocus
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hφ : φ ∈ sourceFiniteGapLocus hp hp1) :
    {j : ℤ | sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet j φ.val ≠ 0}.Finite := by
  apply hφ.subset
  intro j hj hgap
  exact hj (sourceAntiDiscriminant_at_canonicalBoundaryRoot_eq_zero_of_collapsed_gap
    hp hp1 .dirichlet φ.val φ.property j hgap)

end NLS.ZakharovShabat
