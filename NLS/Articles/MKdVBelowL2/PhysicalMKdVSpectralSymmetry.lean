import NLS.Articles.MKdVBelowL2.PhysicalMKdVDiagonal
import NLS.ZakharovShabat.SourceComponentSwapActions

/-! # Actual spectral parity on the physical mKdV diagonal

The unsigned component-swap covariance is consumed on original physical
period-one distributions. Indexed gaps and original Birkhoff action products
are even; the actual canonical root is odd in the spectral variable. The
phase-angle correspondence of equation (50) is a further obligation.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual physical mKdV discriminant is even, with no Hilbert or
finite-gap restriction. -/
theorem physicalMKdV_discriminant_even (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalMKdVInput p) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential (physicalCoefficients u.val.val)) (-z) =
      canonicalDiscriminant hp (periodOnePotential (physicalCoefficients u.val.val)) z :=
  sourceDiscriminant_even_of_diagonal hp hp1 _
    ((mem_physicalMKdVSubspace_iff_source u.val).mp u.property) z

/-- The actual signed-index periodic gaps are even on every physical real
mKdV datum, including collapsed gaps. -/
theorem physicalMKdV_periodicGap_even (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalMKdVInput p) (n : ℤ) :
    sourcePeriodicGapDisplacement hp hp1 (physicalCoefficients u.val.val) (-n) =
      sourcePeriodicGapDisplacement hp hp1 (physicalCoefficients u.val.val) n :=
  sourcePeriodicGapDisplacement_even_of_diagonal hp hp1 _
    ((mem_physicalMKdVSubspace_iff_source u.val).mp u.property) n

/-- The branch of the full canonical root has the original odd spectral
parity on every physical real mKdV datum. -/
theorem physicalMKdV_canonicalRoot_odd (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalMKdVInput p) (z : ℂ) :
    sourceCanonicalRoot hp hp1 (physicalCoefficients u.val.val) (-z) =
      -sourceCanonicalRoot hp hp1 (physicalCoefficients u.val.val) z :=
  sourceCanonicalRoot_odd_of_diagonal hp hp1 _
    ((mem_physicalMKdVSubspace_iff_source u.val).mp u.property) z

/-- The original spectral actions are even at every signed index on the
actual physical diagonal. They are not defined by the desired symmetry. -/
theorem physicalMKdV_complexAction_even (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalMKdVInput p) (n : ℤ) :
    sourceComplexAction hp hp1 (-n) (physicalCoefficients u.val.val) =
      sourceComplexAction hp hp1 n (physicalCoefficients u.val.val) :=
  sourceComplexAction_even_of_diagonal hp hp1 (physicalRealCoefficientsCL u.val)
    ((mem_physicalMKdVSubspace_iff_source u.val).mp u.property) n

/-- The actual coordinate products of the fixed Theorem 1.2 physical
Birkhoff family have the same signed-index symmetry on the mKdV diagonal. -/
theorem physicalMKdV_birkhoff_actions_even (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalMKdVInput p) (n : ℤ) :
    (compatibleBirkhoff hp hp1 u.val.val).1 (-n)*(compatibleBirkhoff hp hp1 u.val.val).2 (-n) =
      (compatibleBirkhoff hp hp1 u.val.val).1 n*(compatibleBirkhoff hp hp1 u.val.val).2 n := by
  have hu := (physicalFourthCandidateDomain_open_real hp hp1).2 u.val
  rw [compatibleBirkhoff_action_on_fourthDomain hp hp1 u.val.val hu (-n),
    compatibleBirkhoff_action_on_fourthDomain hp hp1 u.val.val hu n]
  exact physicalMKdV_complexAction_even hp hp1 u n

end NLS.Articles.MKdVBelowL2
