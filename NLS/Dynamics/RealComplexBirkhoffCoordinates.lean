import NLS.Dynamics.ComplexBirkhoffCoordinates

/-! # Real source coordinates for the complex phase flow

Encoding real rectangular coordinates and decoding conjugate complex pairs
are mutually inverse continuous real linear operations. This allows the
complex phase flow to be lifted through the existing real Birkhoff inverse.
-/
noncomputable section
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS.Birkhoff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Encode the real rectangular pair as complex Birkhoff coordinates. -/
def encodeReal : (RealCoeff p × RealCoeff p) →L[ℝ] (Coeff p × Coeff p) :=
  (rectangularToComplex (p := p)).toContinuousLinearMap.restrictScalars ℝ |>.comp
    ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p))

/-- Recover the real rectangular pair from complex coordinates. -/
def decodeReal : (Coeff p × Coeff p) →L[ℝ] (RealCoeff p × RealCoeff p) :=
  ((Coeff.reCLM p).prodMap (Coeff.reCLM p)).comp
    ((rectangularToComplex (p := p)).symm.toContinuousLinearMap.restrictScalars ℝ)

@[simp] theorem decodeReal_encodeReal (z : RealCoeff p × RealCoeff p) :
    decodeReal (encodeReal z) = z := by
  change ((Coeff.reCLM p).prodMap (Coeff.reCLM p))
    (rectangularToComplex.symm (rectangularToComplex
      (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z))) = z
  rw [ContinuousLinearEquiv.symm_apply_apply]
  apply Prod.ext <;> exact RealCoeff.reCLM_complexCLM p _

/-- Encoding real rectangular coordinates lands on the correct real locus. -/
theorem encodeReal_real (z : RealCoeff p × RealCoeff p) : IsConjugatePair (encodeReal z) := by
  apply rectangularToComplex_real
  intro n
  exact ⟨Complex.ofReal_im _,Complex.ofReal_im _⟩

/-- Conjugate pairs decode to genuinely real rectangular complex coordinates. -/
theorem rectangularToComplex_symm_im_zero (z : Coeff p × Coeff p) (hz : IsConjugatePair z) (n : ℤ) :
    ((rectangularToComplex.symm z).1 n).im = 0 ∧ ((rectangularToComplex.symm z).2 n).im = 0 := by
  have h : conj (z.2 n) = z.1 n := by rw [hz n, conj_conj]
  constructor
  · apply Complex.conj_eq_iff_im.mp
    simp only [rectangularToComplex_symm_fst, map_mul, map_add, conj_complexCoordinateScale, h, ← hz n]
    ring
  · apply Complex.conj_eq_iff_im.mp
    simp only [rectangularToComplex_symm_snd, map_mul, map_sub, conj_complexCoordinateScale,
      Complex.conj_I, h, ← hz n]
    ring

/-- Decoding and re-encoding retain every conjugate complex pair exactly. -/
theorem encodeReal_decodeReal (z : Coeff p × Coeff p) (hz : IsConjugatePair z) :
    encodeReal (decodeReal z) = z := by
  have he : ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p))
      (((Coeff.reCLM p).prodMap (Coeff.reCLM p)) (rectangularToComplex.symm z)) =
      rectangularToComplex.symm z := by
    apply Prod.ext
    · exact RealCoeff.complexCLM_reCLM p _ (fun n => (rectangularToComplex_symm_im_zero z hz n).1)
    · exact RealCoeff.complexCLM_reCLM p _ (fun n => (rectangularToComplex_symm_im_zero z hz n).2)
  change rectangularToComplex (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p))
    (((Coeff.reCLM p).prodMap (Coeff.reCLM p)) (rectangularToComplex.symm z))) = z
  rw [he, ContinuousLinearEquiv.apply_symm_apply]

/-- Real encoding is injective, so equal complex trajectories identify real states. -/
theorem encodeReal_injective : Function.Injective (encodeReal (p := p)) := by
  intro x y h
  simpa only [decodeReal_encodeReal] using congrArg decodeReal h

end NLS.Birkhoff
