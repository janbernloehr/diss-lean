import NLS.Poisson.RegularSourceCotangent
import NLS.SequenceSpaces.WeightedSingle
import NLS.SequenceSpaces.SobolevPairCotangent

/-! # Regular cotangents on weighted source spaces

Square-summable values on raw unit Fourier directions give an intrinsic,
absolutely convergent physical Poisson pairing. The directions have raw
coefficient one; their weighted norms need not equal one.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A weighted continuous cotangent with verified square-summable raw Fourier values. -/
structure WeightedRegularSourceCotangent (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  toCotangent : WeightedCoeffPair w p →L[ℂ] ℂ
  coefficients : Coeff 2 × Coeff 2
  fst_eq : ∀ n : ℤ, coefficients.1 n =
    toCotangent (WeightedCoeffPair.inlCLM w (WeightedCoeff.single w n 1))
  snd_eq : ∀ n : ℤ, coefficients.2 n =
    toCotangent (WeightedCoeffPair.inrCLM w (WeightedCoeff.single w n 1))

namespace WeightedRegularSourceCotangent
variable {w : Weight}

/-- The physical pairing, with the original frequency reversal and factor -i. -/
def bivector (L M : WeightedRegularSourceCotangent w p) : ℂ :=
  hilbertPairBivector L.coefficients M.coefficients

theorem coefficients_eq_of_toCotangent_eq (L M : WeightedRegularSourceCotangent w p)
    (h : L.toCotangent = M.toCotangent) : L.coefficients = M.coefficients := by
  apply Prod.ext <;> ext n
  · rw [L.fst_eq,M.fst_eq,h]
  · rw [L.snd_eq,M.snd_eq,h]

theorem bivector_antisymm (L M : WeightedRegularSourceCotangent w p) :
    L.bivector M = -M.bivector L := hilbertPairBivector_antisymm _ _

@[simp] theorem bivector_self (L : WeightedRegularSourceCotangent w p) : L.bivector L = 0 :=
  hilbertPairBivector_self _

/-- The bracket does not depend on the choice of coefficient witnesses. -/
theorem bivector_congr {L L' M M' : WeightedRegularSourceCotangent w p}
    (hL : L.toCotangent = L'.toCotangent) (hM : M.toCotangent = M'.toCotangent) :
    L.bivector M = L'.bivector M' := by
  unfold bivector
  rw [coefficients_eq_of_toCotangent_eq L L' hL,coefficients_eq_of_toCotangent_eq M M' hM]

theorem norm_bivector_le (L M : WeightedRegularSourceCotangent w p) :
    ‖L.bivector M‖ ≤ 2 * ‖L.coefficients‖ * ‖M.coefficients‖ :=
  norm_hilbertPairBivector_le _ _

theorem summable_norm (L M : WeightedRegularSourceCotangent w p) :
    Summable (fun n : ℤ => ‖
      L.toCotangent (WeightedCoeffPair.inlCLM w (WeightedCoeff.single w n 1)) *
        M.toCotangent (WeightedCoeffPair.inrCLM w (WeightedCoeff.single w (-n) 1)) -
      L.toCotangent (WeightedCoeffPair.inrCLM w (WeightedCoeff.single w n 1)) *
        M.toCotangent (WeightedCoeffPair.inlCLM w (WeightedCoeff.single w (-n) 1))‖) := by
  have h := ((summable_norm_reflectedHilbertPairing L.coefficients.1 M.coefficients.2).of_norm.sub
    (summable_norm_reflectedHilbertPairing L.coefficients.2 M.coefficients.1).of_norm).norm
  simpa only [L.fst_eq,L.snd_eq,M.fst_eq,M.snd_eq] using h

/-- The absolutely convergent Fourier formula uses the actual weighted functional values. -/
theorem bivector_eq_tsum (L M : WeightedRegularSourceCotangent w p) :
    L.bivector M = -Complex.I * ∑' n : ℤ,
      (L.toCotangent (WeightedCoeffPair.inlCLM w (WeightedCoeff.single w n 1)) *
        M.toCotangent (WeightedCoeffPair.inrCLM w (WeightedCoeff.single w (-n) 1)) -
      L.toCotangent (WeightedCoeffPair.inrCLM w (WeightedCoeff.single w n 1)) *
        M.toCotangent (WeightedCoeffPair.inlCLM w (WeightedCoeff.single w (-n) 1))) := by
  rw [bivector,hilbertPairBivector_apply,reflectedHilbertPairing_apply,
    reflectedHilbertPairing_apply,
    ← (summable_norm_reflectedHilbertPairing L.coefficients.1 M.coefficients.2).of_norm.tsum_sub
      (summable_norm_reflectedHilbertPairing L.coefficients.2 M.coefficients.1).of_norm]
  simp only [L.fst_eq,L.snd_eq,M.fst_eq,M.snd_eq]

end WeightedRegularSourceCotangent

end NLS.Poisson
