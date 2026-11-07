import NLS.KdV.SingularHillResolventFamily
import NLS.KdV.SingularHillSemibounded
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! Compact Fredholm theory of the original full-domain Hill operator for
EVERY original complex H-minus-one potential. No endpoint membership is assumed. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The actual singular multiplication is compact on the full original H1
domain for EVERY original H-minus-one potential. -/
theorem isCompactOperator_hminusOneMultiplication
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) : IsCompactOperator (hminusOneMultiplication q) := by
  let U := (sobolevCoefficients (L := 2) (-1) 2).symm
  have hc : IsClosed {a : WeightedCoeff (Weight.sobolev (-1)) 2 |
      IsCompactOperator (hminusOneMultiplication (U a))} :=
    isClosed_setOfPred_isCompactOperator.preimage
      ((hminusOneMultiplicationFamily (L := 2)).continuous.comp U.continuous)
  have hf (a : ℤ →₀ ℂ) : IsCompactOperator
      (hminusOneMultiplication (U (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 a))) := by
    let v := WeightedCoeff.ofFinsupp (SpectralWeight.one.negativeSobolev 0) ⊤ a
    have he : U (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 a) =
        endpointHillHminusOne SpectralWeight.one 0 (by norm_num) v := by
      apply Subtype.ext
      apply Distribution.ext_coefficients
      intro k
      rw [endpointHillHminusOne_coefficient]
      change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val k = _
      rw [LinearIsometryEquiv.apply_symm_apply]
      rfl
    rw [he]
    exact isCompactOperator_endpointH1Multiplication_physical 0 (by norm_num) (by norm_num) v
  have hh : IsCompactOperator (hminusOneMultiplication (U (sobolevCoefficients (-1) 2 q))) :=
    (WeightedCoeff.denseRange_ofFinsupp (Weight.sobolev (-1)) 2 (by norm_num)).induction_on
      (sobolevCoefficients (-1) 2 q) hc hf
  simpa only [U, LinearIsometryEquiv.symm_apply_apply] using hh

/-- The normalized original pencil is identity plus compact at EVERY complex
spectral parameter and EVERY complex original H-minus-one potential. -/
theorem singularHillNormalizedPencil_sub_one
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    singularHillNormalizedPencil q z-1 = singularHillFreeInverse.comp
      (hminusOneMultiplication q-(z+1) • singularHillDomainInclusion) := by
  apply ContinuousLinearMap.ext
  intro f
  change singularHillFreeInverse
    (singularHillLaplacian f+hminusOneMultiplication q f-z • singularHillDomainInclusion f)-f =
      singularHillFreeInverse (hminusOneMultiplication q f-(z+1) • singularHillDomainInclusion f)
  have hid : singularHillFreeInverse (singularHillLaplacian f+singularHillDomainInclusion f) = f :=
    singularHillFreeInverse_shift f
  calc
    _ = singularHillFreeInverse
        (singularHillLaplacian f+hminusOneMultiplication q f-z • singularHillDomainInclusion f)-
        singularHillFreeInverse (singularHillLaplacian f+singularHillDomainInclusion f) := by rw [hid]
    _ = singularHillFreeInverse ((singularHillLaplacian f+hminusOneMultiplication q f-
        z • singularHillDomainInclusion f)-(singularHillLaplacian f+singularHillDomainInclusion f)) :=
      (map_sub _ _ _).symm
    _ = _ := by congr 1; rw [add_smul, one_smul]; abel

/-- Compactness is in the exact original H1 operator norm. -/
theorem isCompactOperator_singularHillNormalizedPencil_sub_one
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    IsCompactOperator (singularHillNormalizedPencil q z-1 :
      FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2) := by
  rw [singularHillNormalizedPencil_sub_one]
  exact ((isCompactOperator_hminusOneMultiplication q).sub
    (isCompactOperator_singularHillDomainInclusion.smul (z+1))).clm_comp singularHillFreeInverse

/-- The full original H-minus-one Hill pencil has Fredholm index zero. -/
theorem singularHillNormalizedPencil_fredholm_index_zero
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    (singularHillNormalizedPencil q z).IsFredholm ∧
      Module.finrank ℂ (singularHillNormalizedPencil q z).ker =
        Module.finrank ℂ ((FourierLebesgueSpace (2:ℝ) 1 2) ⧸ (singularHillNormalizedPencil q z).range) :=
  CompactSpectrum.fredholm_index_zero_of_compact_sub_smul _ (by norm_num : (1:ℂ) ≠ 0)
    (by simpa only [one_smul] using isCompactOperator_singularHillNormalizedPencil_sub_one q z)

/-- Injectivity implies full original-domain bijectivity for every H-minus-one input. -/
theorem singularHillNormalizedPencil_bijective_of_injective
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (hi : Function.Injective (singularHillNormalizedPencil q z)) :
    Function.Bijective (singularHillNormalizedPencil q z) :=
  CompactScalarPerturbation.bijective_of_injective _ (by norm_num : (1:ℂ) ≠ 0)
    (by simpa only [one_smul] using isCompactOperator_singularHillNormalizedPencil_sub_one q z) hi

/-- The normalized kernel is EXACTLY the full original H1 eigen-equation. -/
theorem singularHillNormalizedPencil_apply_eq_zero_iff
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillNormalizedPencil q z f = 0 ↔ singularHillOperator q f = z • singularHillDomainInclusion f := by
  constructor
  · intro h
    have he := congrArg singularHillFreeShift h
    change singularHillFreeShift (singularHillFreeInverse
      (singularHillOperator q f-z • singularHillDomainInclusion f)) = singularHillFreeShift 0 at he
    rw [singularHillFreeShift_inverse, map_zero] at he
    exact sub_eq_zero.mp he
  · intro h
    change singularHillFreeInverse (singularHillOperator q f-z • singularHillDomainInclusion f) = 0
    rw [h, sub_self, map_zero]

/-- There are no actual spectral points other than full-domain eigenvalues. -/
theorem not_mem_singularHillResolventSet_iff
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    z ∉ singularHillResolventSet q ↔ ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
      singularHillOperator q f = z • singularHillDomainInclusion f := by
  rw [mem_singularHillResolventSet_iff_isUnit, ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · intro h
    by_contra hn
    apply h
    apply singularHillNormalizedPencil_bijective_of_injective q z
    intro f g hfg
    apply sub_eq_zero.mp
    have he : singularHillNormalizedPencil q z (f-g) = 0 := by rw [map_sub, hfg, sub_self]
    by_contra hne
    exact hn ⟨f-g,hne,(singularHillNormalizedPencil_apply_eq_zero_iff q z (f-g)).mp he⟩
  · rintro ⟨f,hf0,hf⟩ h
    apply hf0
    exact h.1 (((singularHillNormalizedPencil_apply_eq_zero_iff q z f).mpr hf).trans (map_zero _).symm)

/-- An explicit entire left half-plane belongs to the actual full resolvent. -/
theorem mem_singularHillResolventSet_of_re_lt
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (hz : z.re < -singularHillLowerBoundConstant ‖q‖) : z ∈ singularHillResolventSet q := by
  by_contra hn
  obtain ⟨f,hf0,hf⟩ := (not_mem_singularHillResolventSet_iff q z).mp hn
  exact (singularHill_eigenvalue_re_lower_bound q z f hf0 hf).not_gt hz

/-- Every complex original H-minus-one potential has an ACTUAL nonempty resolvent. -/
theorem singularHillResolventSet_nonempty (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    (singularHillResolventSet q).Nonempty := by
  refine ⟨(-singularHillLowerBoundConstant ‖q‖-1:ℝ), mem_singularHillResolventSet_of_re_lt q _ ?_⟩
  simp only [Complex.ofReal_re]
  linarith

end NLS.KdV
