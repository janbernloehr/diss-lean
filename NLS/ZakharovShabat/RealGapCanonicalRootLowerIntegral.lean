import NLS.ZakharovShabat.RealGapCanonicalRootUpperIntegral

/-!
# The lower canonical-root boundary integral on a real gap

The lower canonical-root boundary value is the negative of the upper
one at the same real spectral point. Hence its discriminant-derivative
quotient integral vanishes along with the upper-side integral.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical-root lower-side value indexed by a real spectral
point in a gap. -/
def realGapCanonicalRootLowerValue (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (x : ℝ) : ℂ :=
  sourceCanonicalRootGapLowerValue hp hp1 ψ n
    (realGapInverseCoordinate hp hp1 ψ n x)

/-- The two real-coordinate canonical-root boundary values are
opposites, including at the gap endpoints. -/
theorem realGapCanonicalRootLowerValue_eq_neg_upper
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (x : ℝ) :
    realGapCanonicalRootLowerValue hp hp1 ψ n x =
      -realGapCanonicalRootUpperValue hp hp1 ψ n x := by
  unfold realGapCanonicalRootLowerValue realGapCanonicalRootUpperValue
  have h := sourceCanonicalRootGapUpperValue_eq_neg_lower hp hp1 ψ n
    (realGapInverseCoordinate hp hp1 ψ n x)
  rw [h]
  simp

/-- The lower-side real-gap boundary quotient integral vanishes. -/
theorem integral_discriminant_derivative_div_realGapCanonicalRootLowerValue_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (∫ x in (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re..
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re,
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) /
        realGapCanonicalRootLowerValue hp hp1 ψ n x) = 0 := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n).re
  let D (x : ℝ) := deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ)
  let U := realGapCanonicalRootUpperValue hp hp1 ψ n
  let L := realGapCanonicalRootLowerValue hp hp1 ψ n
  calc
    (∫ x in a..b, D x / L x) =
        ∫ x in a..b, -(D x / U x) := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      have hLU : L x = -U x :=
        realGapCanonicalRootLowerValue_eq_neg_upper hp hp1 ψ n x
      change D x / L x = -(D x / U x)
      rw [hLU]
      simp only [div_neg]
    _ = -(∫ x in a..b, D x / U x) := by rw [intervalIntegral.integral_neg]
    _ = 0 := by
      rw [integral_discriminant_derivative_div_realGapCanonicalRootUpperValue_eq_zero
        hp hp1 ψ hreal n hopen]
      simp

end NLS.ZakharovShabat
