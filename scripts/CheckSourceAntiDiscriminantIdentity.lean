import NLS.ZakharovShabat.SourceAntiDiscriminantIdentity

open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

example (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    periodOneBoundaryCharacteristic (by simp) (by norm_num) b
      (CoeffPair.ofFinsupp (p := 2) a) z =
        classicalSeparatedCharacteristic b (finiteSourceCurve a) z :=
  periodOneBoundaryCharacteristic_finite_eq_classical b a z

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4 =
      (sourceAntiDiscriminantCandidate hp hp1 φ z)^2 -
        4 * periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z *
          periodOneBoundaryCharacteristic hp hp1 .neumann φ z :=
  sourceDiscriminant_sq_sub_four hp hp1 φ z

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    (canonicalDiscriminant hp (periodOnePotential φ)
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n))^2-4 =
      (sourceAntiDiscriminantCandidate hp hp1 φ
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n))^2 :=
  sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 φ n

end NLS.ZakharovShabat
