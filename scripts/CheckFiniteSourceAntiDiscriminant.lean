import NLS.ZakharovShabat.FiniteSourceAntiDiscriminant

open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

example (b : BoundaryCondition) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) b
      (CoeffPair.ofFinsupp (p := 2) a) z =
        classicalAuxiliaryCharacteristic b (finiteSourceCurve a) z :=
  auxiliaryPeriodOneCharacteristic_finite_eq_classical b a z

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (z : ℂ) :
    sourceAntiDiscriminantCandidate hp hp1
      (CoeffPair.ofFinsupp (p := p) a) z =
        classicalAntiDiscriminant (finiteSourceCurve a) z :=
  sourceAntiDiscriminantCandidate_finite_eq_classical_of_exponent hp hp1 a z

example {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (F : CoeffPair p → ℂ) (hF : Continuous F)
    (hfinite : ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ),
      F (CoeffPair.ofFinsupp (p := p) a) =
        classicalAntiDiscriminant (finiteSourceCurve a) z) :
    F = fun φ => sourceAntiDiscriminantCandidate hp hp1 φ z :=
  sourceAntiDiscriminantCandidate_unique_continuous hp hp1 z F hF hfinite

end NLS.ZakharovShabat
