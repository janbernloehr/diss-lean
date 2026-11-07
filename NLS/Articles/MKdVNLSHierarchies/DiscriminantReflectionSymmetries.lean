import NLS.ZakharovShabat.SourceMidpointReflection

/-! # The P and T clauses of Theorem 6(i)–(iii)

These are identities of the actual source discriminant and its full Fréchet
cotangent, on every finite complex source space p>1, in particular the
original H0=L2 domain. The phase, endpoint-label, canonical-root and spatial
ODE clauses of Theorem 6 are separate obligations.
-/
noncomputable section
open Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.MKdVNLSHierarchies
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem theorem6_i_swap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential φ) z =
      canonicalDiscriminant hp (periodOnePotential (sourceComponentSwap φ)) (-z) :=
  (sourceDiscriminant_componentSwap hp hp1 φ z).symm

theorem theorem6_i_reflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential φ) z =
      canonicalDiscriminant hp (periodOnePotential (sourceMidpointReflection φ)) (-z) :=
  (sourceDiscriminant_midpointReflection hp hp1 φ z).symm

theorem theorem6_ii_swap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    deriv (canonicalDiscriminant hp (periodOnePotential φ)) z =
      -deriv (canonicalDiscriminant hp (periodOnePotential (sourceComponentSwap φ))) (-z) := by
  rw [sourceDiscriminant_deriv_componentSwap hp hp1,neg_neg]

theorem theorem6_ii_reflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    deriv (canonicalDiscriminant hp (periodOnePotential φ)) z =
      -deriv (canonicalDiscriminant hp (periodOnePotential (sourceMidpointReflection φ))) (-z) := by
  rw [sourceDiscriminant_deriv_midpointReflection hp hp1,neg_neg]

theorem theorem6_iii_swap_covectors (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceDiscriminantCotangent hp z φ =
      (sourceDiscriminantCotangent hp (-z) (sourceComponentSwap φ)).comp
        sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap :=
  sourceDiscriminantCotangent_componentSwap hp hp1 φ z

theorem theorem6_iii_reflection_covectors (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceDiscriminantCotangent hp z φ =
      (sourceDiscriminantCotangent hp (-z) (sourceMidpointReflection φ)).comp
        sourceMidpointReflection.toContinuousLinearEquiv.toContinuousLinearMap :=
  sourceDiscriminantCotangent_midpointReflection hp hp1 φ z

end NLS.Articles.MKdVNLSHierarchies
