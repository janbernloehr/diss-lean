import NLS.ZakharovShabat.SourceAntiDiscriminantCentralLp

open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (R : ℝ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ ∈ U, ∀ z : ℂ, ‖z‖ ≤ R →
        ‖sourceAntiDiscriminantCandidate hp hp1 ψ z‖ ≤ B ∧
          ‖deriv (sourceAntiDiscriminantCandidate hp hp1 ψ) z‖ ≤ B :=
  exists_local_uniform_sourceAntiDiscriminant_on_ball hp hp1 φ R

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U,
        ∃ a b : Coeff p, ‖a‖ ≤ K ∧ ‖b‖ ≤ K ∧
          (∀ n, a n = sourceAntiDiscriminantCandidate hp hp1 ψ
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)) ∧
          (∀ n, b n = deriv (sourceAntiDiscriminantCandidate hp hp1 ψ)
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)) :=
  exists_local_uniform_sampled_sourceAntiDiscriminant_at_dirichletRoots hp hp1 φ

end NLS.ZakharovShabat
