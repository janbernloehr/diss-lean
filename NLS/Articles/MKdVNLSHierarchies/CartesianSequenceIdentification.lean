import NLS.MKdV.MiuraL2CartesianProperness

/-! # The full native Cartesian map for the physical mKdV actions

The original complex L² map takes values in the full weighted Hilbert
pair of order one half. Its quadratic action projection is exactly the
independent physical action sequence, and with signed mean its real map
is proper. Infinite-dimensional invertibility and Gardner canonicity
remain separate essential obligations.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- The full native Cartesian map has a Banach power series near every
original physical real L² profile, including all closed actions. -/
theorem native_cartesian_L2_sequence_analytic
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    AnalyticAt ℂ miuraL2CartesianSequence a := analyticAt_miuraL2CartesianSequence a ha

/-- Every original positive coordinate survives the weighted realization. -/
theorem native_cartesian_L2_sequence_positive
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((miuraL2CartesianSequence a).1.val n,(miuraL2CartesianSequence a).2.val n) =
      miuraL2CartesianCoordinates n a := miuraL2CartesianSequence_positive a ha n hn

/-- The full native quadratic radii recover the actual original action map. -/
theorem native_cartesian_L2_actions_recovered
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    miuraL2CartesianActions (miuraL2CartesianSequence a) = miuraL2ActionSequence a :=
  miuraL2CartesianActions_sequence_eq a ha

/-- The full native Cartesian pair and literal signed mean give a proper
map in original physical L², including zero mean and closed gaps. -/
theorem native_cartesian_L2_mean_map_proper : IsProperMap miuraRealL2CartesianMeanMap :=
  isProperMap_miuraRealL2CartesianMeanMap

/-- All complete native Cartesian and signed-mean fibers are compact. -/
theorem native_cartesian_L2_mean_fiber_compact (z : MiuraL2CartesianTarget × ℂ) :
    IsCompact {a : MiuraRealL2 | miuraRealL2CartesianMeanMap a = z} :=
  isCompact_miuraRealL2CartesianMeanFiber z

end NLS.Articles.MKdVNLSHierarchies
