import NLS.ZakharovShabat.ClassicalAuxiliaryCharacteristics
import NLS.ZakharovShabat.ExponentAuxiliaryBoundaryCoordinates
import NLS.ZakharovShabat.SourcePhaseCompatibility

/-! # Normalized source candidate for the anti-discriminant

The difference of the normalized actual auxiliary characteristics has the
sign dictated by the true auxiliary endpoint domains. It is jointly analytic
on the original finite-exponent source space, has an exact difference-of-
products formula, and vanishes at the free potential. Identification with
the classical monodromy anti-trace on a dense physical subspace remains a
separate normalization theorem.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source-space candidate selected by the actual auxiliary endpoint conditions. -/
def sourceAntiDiscriminantCandidate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) : ℂ :=
  auxiliaryPeriodOneCharacteristic hp hp1 .neumann φ z -
    auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet φ z

/-- The candidate is entire in the spectral parameter. -/
theorem analyticOnNhd_sourceAntiDiscriminantCandidate (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    AnalyticOnNhd ℂ (sourceAntiDiscriminantCandidate hp hp1 φ) univ := by
  intro z _
  exact (analyticOnNhd_auxiliaryPeriodOneCharacteristic hp hp1 .neumann φ z (mem_univ _)).sub
    (analyticOnNhd_auxiliaryPeriodOneCharacteristic hp hp1 .dirichlet φ z (mem_univ _))

/-- It is jointly complex analytic in the spectral parameter and source coefficients. -/
theorem analyticOnNhd_sourceAntiDiscriminantCandidate_joint (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ (fun q : ℂ × CoeffPair p =>
      sourceAntiDiscriminantCandidate hp hp1 q.2 q.1) univ := by
  intro q _
  exact (analyticOnNhd_auxiliaryPeriodOneCharacteristic_joint hp hp1 .neumann q (mem_univ _)).sub
    (analyticOnNhd_auxiliaryPeriodOneCharacteristic_joint hp hp1 .dirichlet q (mem_univ _))

/-- The literal entire expression is the difference of the two actual starred canonical products. -/
theorem sourceAntiDiscriminantCandidate_eq_products (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceAntiDiscriminantCandidate hp hp1 φ z =
      boundaryCharacteristicProduct (canonicalAuxiliaryPeriodOneRoots hp hp1 .neumann φ) z -
        boundaryCharacteristicProduct (canonicalAuxiliaryPeriodOneRoots hp hp1 .dirichlet φ) z := by
  simp only [sourceAntiDiscriminantCandidate,
    auxiliaryPeriodOneCharacteristic_eq_canonicalProduct]

/-- At zero potential the two normalized sine functions cancel. -/
@[simp] theorem sourceAntiDiscriminantCandidate_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (z : ℂ) :
    sourceAntiDiscriminantCandidate hp hp1 (0 : CoeffPair p) z = 0 := by
  simp [sourceAntiDiscriminantCandidate]

/-- The candidate agrees exactly across finite coefficient exponents. -/
theorem sourceAntiDiscriminantCandidate_exponent {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (h : p ≤ q)
    (φ : CoeffPair p) :
    sourceAntiDiscriminantCandidate hp hp1 φ =
      sourceAntiDiscriminantCandidate hq hq1 (CoeffPair.exponentInclusion h φ) := by
  funext z
  simp only [sourceAntiDiscriminantCandidate]
  rw [auxiliaryPeriodOneCharacteristic_exponent hp hq hp1 hq1 h .neumann φ,
    auxiliaryPeriodOneCharacteristic_exponent hp hq hp1 hq1 h .dirichlet φ]

end NLS.ZakharovShabat
