import NLS.Dynamics.ComplexPhaseFlow
import NLS.SequenceSpaces.RealCoeff

/-! # Complex and rectangular Birkhoff coordinates

The change of variables z=(x-iy)/sqrt(2), w=(x+iy)/sqrt(2) is a continuous
linear equivalence at every Banach sequence exponent. It turns the quadratic
rectangular action into the product zw and real rectangular coordinates
into same-index conjugate pairs, as used in Section 22.
-/
noncomputable section
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Normalizing factor in the complex Birkhoff coordinates. -/
def complexCoordinateScale : ℂ := (Real.sqrt 2 : ℂ)⁻¹

private theorem complexCoordinateScale_sq : complexCoordinateScale^2 = (1/2 : ℂ) := by
  have h : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [complexCoordinateScale, inv_pow, h]
  norm_num

@[simp] theorem conj_complexCoordinateScale : conj complexCoordinateScale = complexCoordinateScale := by
  simp [complexCoordinateScale]

private def rectangularToComplexCLM : (Coeff p × Coeff p) →L[ℂ] (Coeff p × Coeff p) :=
  ((complexCoordinateScale • ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)) -
    (complexCoordinateScale*I) • ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).prod
  ((complexCoordinateScale • ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)) +
    (complexCoordinateScale*I) • ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))

private def complexToRectangularCLM : (Coeff p × Coeff p) →L[ℂ] (Coeff p × Coeff p) :=
  ((complexCoordinateScale • ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)) +
    complexCoordinateScale • ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).prod
  (((I*complexCoordinateScale) • ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)) -
    (I*complexCoordinateScale) • ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))

private theorem rectangularToComplexCLM_fst (z : Coeff p × Coeff p) (n : ℤ) :
    (rectangularToComplexCLM z).1 n = complexCoordinateScale*(z.1 n-I*z.2 n) := by
  change complexCoordinateScale*z.1 n-(complexCoordinateScale*I)*z.2 n = _
  ring

private theorem rectangularToComplexCLM_snd (z : Coeff p × Coeff p) (n : ℤ) :
    (rectangularToComplexCLM z).2 n = complexCoordinateScale*(z.1 n+I*z.2 n) := by
  change complexCoordinateScale*z.1 n+(complexCoordinateScale*I)*z.2 n = _
  ring

private theorem complexToRectangularCLM_fst (z : Coeff p × Coeff p) (n : ℤ) :
    (complexToRectangularCLM z).1 n = complexCoordinateScale*(z.1 n+z.2 n) := by
  change complexCoordinateScale*z.1 n+complexCoordinateScale*z.2 n = _
  ring

private theorem complexToRectangularCLM_snd (z : Coeff p × Coeff p) (n : ℤ) :
    (complexToRectangularCLM z).2 n = I*complexCoordinateScale*(z.1 n-z.2 n) := by
  change (I*complexCoordinateScale)*z.1 n-(I*complexCoordinateScale)*z.2 n = _
  ring

/-- The exact continuous linear change between rectangular and complex coordinates. -/
def rectangularToComplex : (Coeff p × Coeff p) ≃L[ℂ] (Coeff p × Coeff p) :=
  ContinuousLinearEquiv.equivOfInverse rectangularToComplexCLM complexToRectangularCLM
    (by
      intro z
      apply Prod.ext <;> ext n
      · rw [complexToRectangularCLM_fst, rectangularToComplexCLM_fst, rectangularToComplexCLM_snd]
        ring_nf
        rw [complexCoordinateScale_sq]
        ring
      · rw [complexToRectangularCLM_snd, rectangularToComplexCLM_fst, rectangularToComplexCLM_snd]
        ring_nf
        rw [complexCoordinateScale_sq, I_sq]
        ring)
    (by
      intro z
      apply Prod.ext <;> ext n
      · rw [rectangularToComplexCLM_fst, complexToRectangularCLM_fst, complexToRectangularCLM_snd]
        ring_nf
        rw [complexCoordinateScale_sq, I_sq]
        ring
      · rw [rectangularToComplexCLM_snd, complexToRectangularCLM_fst, complexToRectangularCLM_snd]
        ring_nf
        rw [complexCoordinateScale_sq, I_sq]
        ring)

@[simp] theorem rectangularToComplex_fst (z : Coeff p × Coeff p) (n : ℤ) :
    (rectangularToComplex z).1 n = complexCoordinateScale*(z.1 n-I*z.2 n) :=
  rectangularToComplexCLM_fst z n

@[simp] theorem rectangularToComplex_snd (z : Coeff p × Coeff p) (n : ℤ) :
    (rectangularToComplex z).2 n = complexCoordinateScale*(z.1 n+I*z.2 n) :=
  rectangularToComplexCLM_snd z n

@[simp] theorem rectangularToComplex_symm_fst (z : Coeff p × Coeff p) (n : ℤ) :
    (rectangularToComplex.symm z).1 n = complexCoordinateScale*(z.1 n+z.2 n) :=
  complexToRectangularCLM_fst z n

@[simp] theorem rectangularToComplex_symm_snd (z : Coeff p × Coeff p) (n : ℤ) :
    (rectangularToComplex.symm z).2 n = I*complexCoordinateScale*(z.1 n-z.2 n) :=
  complexToRectangularCLM_snd z n

/-- Complex products recover the original rectangular actions exactly. -/
theorem rectangularToComplex_action (z : Coeff p × Coeff p) (n : ℤ) :
    (rectangularToComplex z).1 n*(rectangularToComplex z).2 n = ((z.1 n)^2+(z.2 n)^2)/2 := by
  rw [rectangularToComplex_fst, rectangularToComplex_snd]
  ring_nf
  rw [complexCoordinateScale_sq, I_sq]
  ring

/-- Real rectangular coordinates become same-index conjugate pairs. -/
theorem rectangularToComplex_real (z : Coeff p × Coeff p)
    (hz : ∀ n, (z.1 n).im = 0 ∧ (z.2 n).im = 0) :
    IsConjugatePair (rectangularToComplex z) := by
  intro n
  have hx : conj (z.1 n) = z.1 n := by apply Complex.ext <;> simp [(hz n).1]
  have hy : conj (z.2 n) = z.2 n := by apply Complex.ext <;> simp [(hz n).2]
  simp only [rectangularToComplex_fst,rectangularToComplex_snd,map_mul,map_sub,
    conj_complexCoordinateScale,Complex.conj_I,hx,hy,neg_mul,sub_neg_eq_add]

end NLS.Birkhoff
