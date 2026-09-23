import NLS.ZakharovShabat.SourceAntiDiscriminantDiscLp

open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U,
        ∃ A : Coeff p, ‖A‖ ≤ K ∧
          (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
            ‖sourceAntiDiscriminantCandidate hp hp1 ψ z‖ ≤ ‖A n‖) ∧
          (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
            ‖deriv (sourceAntiDiscriminantCandidate hp hp1 ψ) z‖ ≤
              (4/Real.pi)*‖A n‖) :=
  exists_uniform_sourceAntiDiscriminant_disc_majorants hp hp1 φ

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    ∃ N : ℕ, ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U,
        ∃ A : Coeff p, ‖A‖ ≤ K ∧ ∀ n : ℤ, N < n.natAbs →
          ‖sourceAntiDiscriminantCandidate hp hp1 ψ
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)‖ ≤ ‖A n‖ ∧
          ‖deriv (sourceAntiDiscriminantCandidate hp hp1 ψ)
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)‖ ≤
              (4/Real.pi)*‖A n‖ :=
  exists_uniform_sourceAntiDiscriminant_at_dirichlet_tail hp hp1 φ

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    Memℓp (fun n => sourceAntiDiscriminantCandidate hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)) p ∧
    Memℓp (fun n => deriv (sourceAntiDiscriminantCandidate hp hp1 φ)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)) p :=
  memℓp_sourceAntiDiscriminant_at_dirichletRoots hp hp1 φ

end NLS.ZakharovShabat
