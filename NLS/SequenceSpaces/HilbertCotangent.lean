import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.ExponentEmbedding
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Coefficients of continuous cotangents on Hilbert directions

Conjugating the Riesz representative identifies a complex continuous
linear functional with its unconjugated Fourier coefficients. Restricting
a functional on an exponent at least two to Hilbert directions gives
square-summable coefficients continuously, with an explicit norm bound.
-/

noncomputable section
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Coeff

/-- The coefficient sequence of a complex linear functional on `ell²`.
The extra conjugation converts the Hermitian Riesz map to bilinear duality. -/
def hilbertCotangentCoefficients : (Coeff 2 →L[ℂ] ℂ) →L[ℂ] Coeff 2 :=
  LinearMap.mkContinuous {
    toFun := fun L => star ((InnerProductSpace.toDual ℂ (Coeff 2)).symm L)
    map_add' := by intro L M; simp
    map_smul' := by
      intro z L
      rw [(InnerProductSpace.toDual ℂ (Coeff 2)).symm.map_smulₛₗ,star_smul]
      simp
  } 1 (by intro L; simp)

@[simp] theorem hilbertCotangentCoefficients_apply (L : Coeff 2 →L[ℂ] ℂ) (n : ℤ) :
    hilbertCotangentCoefficients L n = L (lp.single 2 n 1) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := Coeff 2)
    (x := lp.single 2 n 1) (y := L)
  simpa only [hilbertCotangentCoefficients,LinearMap.mkContinuous_apply,
    LinearMap.coe_mk,AddHom.coe_mk,lp.star_apply,lp.inner_single_right,
    RCLike.inner_apply',starRingEnd_apply,mul_one] using h

@[simp] theorem norm_hilbertCotangentCoefficients (L : Coeff 2 →L[ℂ] ℂ) :
    ‖hilbertCotangentCoefficients L‖ = ‖L‖ := by
  simp [hilbertCotangentCoefficients]

/-- The unconjugated coefficients recover the original functional. -/
theorem dualPairing_hilbertCotangentCoefficients (L : Coeff 2 →L[ℂ] ℂ) (h : Coeff 2) :
    dualPairing (hilbertCotangentCoefficients L) h = L h := by
  have hR := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := Coeff 2) (x := h) (y := L)
  simpa only [dualPairing_apply,lp.inner_eq_tsum,RCLike.inner_apply',starRingEnd_apply,
    hilbertCotangentCoefficients,LinearMap.mkContinuous_apply,LinearMap.coe_mk,
    AddHom.coe_mk,lp.star_apply] using hR

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Restriction to Hilbert directions is a bounded linear operation on cotangents. -/
def hilbertCotangentRestriction (h2p : (2:ℝ≥0∞) ≤ p) :
    (Coeff p →L[ℂ] ℂ) →L[ℂ] Coeff 2 :=
  hilbertCotangentCoefficients.comp
    ((ContinuousLinearMap.compL ℂ (Coeff 2) (Coeff p) ℂ).flip (exponentInclusion h2p))

@[simp] theorem hilbertCotangentRestriction_apply (h2p : (2:ℝ≥0∞) ≤ p)
    (L : Coeff p →L[ℂ] ℂ) (n : ℤ) :
    hilbertCotangentRestriction h2p L n = L (lp.single p n 1) := by
  change hilbertCotangentCoefficients (L.comp (exponentInclusion h2p)) n = _
  rw [hilbertCotangentCoefficients_apply]
  change L (exponentInclusion h2p (lp.single 2 n 1)) = L (lp.single p n 1)
  congr 1

theorem norm_hilbertCotangentRestriction_le (h2p : (2:ℝ≥0∞) ≤ p) (L : Coeff p →L[ℂ] ℂ) :
    ‖hilbertCotangentRestriction h2p L‖ ≤ ‖L‖ := by
  change ‖hilbertCotangentCoefficients (L.comp (exponentInclusion h2p))‖ ≤ _
  rw [norm_hilbertCotangentCoefficients]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro h
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_exponentInclusion_le h2p h) (norm_nonneg _))

/-- The restricted coefficient sequence represents the functional on every
Hilbert direction, not only on individual Fourier modes. -/
theorem dualPairing_hilbertCotangentRestriction (h2p : (2:ℝ≥0∞) ≤ p)
    (L : Coeff p →L[ℂ] ℂ) (h : Coeff 2) :
    dualPairing (hilbertCotangentRestriction h2p L) h = L (exponentInclusion h2p h) :=
  dualPairing_hilbertCotangentCoefficients (L.comp (exponentInclusion h2p)) h

end NLS.Coeff
