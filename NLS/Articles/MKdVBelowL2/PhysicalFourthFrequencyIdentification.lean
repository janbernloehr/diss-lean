import NLS.Articles.MKdVBelowL2.PhysicalFourthFrequencyRemainder
import NLS.ZakharovShabat.SourceFiniteGapFourthFrequencyExponent

/-! # Physical H₄ action derivatives and the article's chosen candidate

The accepted Hilbert Birkhoff member supplies the independently defined
physical finite-gap action derivatives, including closed selected actions.
The all-exponent moment identity identifies the same candidate on original
period-one distributions, with its exact mass, momentum and dispersion terms.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The physical finite-gap H₄ frequency uses actual action derivatives of
the fixed Hilbert Birkhoff family, independently of every moment candidate. -/
def physicalFiniteGapFourthFrequency (hp : p ≠ ⊤) (hp1 : 1 < p)
    (u : PhysicalRealInput p)
    (hf : physicalRealCoefficientsCL u ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) : ℂ :=
  (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex.finiteGapFourthFrequencyAtExponent
    hp hp1 (physicalRealCoefficientsCL u) hf n

/-- The chosen physical candidate has the physical normalized H₄ value at
every real finite-gap input and every selected index, including closed actions. -/
theorem physicalFourthFrequencyCandidate_eq_finiteGap_actionDerivative
    (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalRealInput p)
    (hf : physicalRealCoefficientsCL u ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    physicalFourthFrequencyCandidate hp hp1 n u.val = physicalFiniteGapFourthFrequency hp hp1 u hf n-
      6*sourceFiniteGapNLSHamiltonian hp hp1 (physicalRealCoefficientsCL u) hf 2-
      (12*Real.pi:ℂ)*n*sourceFiniteGapNLSHamiltonian hp hp1 (physicalRealCoefficientsCL u) hf 1-
      (2*(n:ℂ)*Real.pi)^3 := by
  exact ((fourthMomentChart hp hp1).atlas.weighted_moments_eq_physical_fourth_finiteGap
    (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
    (fourthMomentChart hp hp1).squared.toSourcePsiIsolatingComplexExtension
    (physicalRealCoefficientsCL u) hf n).symm

end NLS.Articles.MKdVBelowL2
