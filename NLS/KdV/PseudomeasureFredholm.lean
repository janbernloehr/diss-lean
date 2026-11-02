import NLS.KdV.PseudomeasureMultiplication
import NLS.KdV.SingularHillFreeIsomorphism
import NLS.SequenceSpaces.EndpointCompactInclusion
import NLS.FunctionalAnalysis.CompactFredholm
import NLS.FunctionalAnalysis.CompactScalarPerturbation
import NLS.FunctionalAnalysis.CompactAnalyticDeterminant

/-! # Fredholm theory for the actual singular endpoint Hill pencil

The potential multiplication and the original H1-to-H-minus-one inclusion
are compact. A fixed physical free isomorphism normalizes the full pencil
to identity plus compact on H1, for every complex spectral parameter. This
does not restrict an inhomogeneous right-hand side to an endpoint space.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The entire signed weighted endpoint space includes compactly into original H-minus-one. -/
theorem isCompactOperator_endpointHillHminusOne (w : SpectralWeight) (r : ℝ) (hr1 : r < 1/2) :
    IsCompactOperator (endpointHillHminusOne w r hr1) := by
  have h : 1 < (-r-(-1))*(2:ℝ≥0∞).toReal := by norm_num; linarith
  exact ((WeightedCoeff.isCompactOperator_endpointLowerInclusion r (-1)
    (by norm_num) h).comp_clm (w.negativeSobolevToSobolev r ⊤)).clm_comp
      (sobolevCoefficients (L := 2) (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The original physical domain inclusion is compact in the original target norm. -/
theorem isCompactOperator_singularHillDomainInclusion :
    IsCompactOperator singularHillDomainInclusion := by
  let E := (WeightedCoeff.sobolevExponentInclusion
    (s := 1) (t := -(-1:ℝ)) (p := 2) (q := ⊤) (by norm_num) le_top).comp
      (sobolevCoefficients (L := 2) 1 2).toContinuousLinearEquiv.toContinuousLinearMap
  let J := WeightedCoeff.endpointLowerInclusion (-(-1:ℝ)) (-1) (p := 2)
    (by norm_num) (by norm_num)
  let U := (sobolevCoefficients (L := 2) (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hc : IsCompactOperator (U.comp (J.comp E)) :=
    ((WeightedCoeff.isCompactOperator_endpointLowerInclusion (-1) (-1)
      (p := 2) (by norm_num) (by norm_num)).comp_clm E).clm_comp U
  have he : singularHillDomainInclusion = U.comp (J.comp E) := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    apply Distribution.ext_coefficients
    intro k
    rw [singularHillDomainInclusion_coefficient]
    change f.val (mode (-k)) = ((sobolevCoefficients (-1) 2)
      ((sobolevCoefficients (-1) 2).symm (J (E f)))).val k
    rw [LinearIsometryEquiv.apply_symm_apply]
    simp only [J, E, ContinuousLinearMap.comp_apply, WeightedCoeff.endpointLowerInclusion_apply,
      WeightedCoeff.sobolevExponentInclusion_apply, ContinuousLinearEquiv.coe_coe]
    rfl
  rw [he]
  exact hc

/-- For a singular endpoint potential, actual multiplication is compact on the full original H1 domain. -/
theorem isCompactOperator_endpointH1Multiplication_physical (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    IsCompactOperator (hminusOneMultiplication (endpointHillHminusOne SpectralWeight.one r hr1 q)) := by
  have he : hminusOneMultiplication (endpointHillHminusOne SpectralWeight.one r hr1 q) =
      (endpointHillHminusOne SpectralWeight.one r hr1).comp (endpointH1Multiplication r hr hr1 q) := by
    apply ContinuousLinearMap.ext
    intro f
    exact (endpointH1Multiplication_physical r hr hr1 q f).symm
  rw [he]
  exact (isCompactOperator_endpointHillHminusOne SpectralWeight.one r hr1).comp_clm
    (endpointH1Multiplication r hr hr1 q)

/-- The actual original singular Hill spectral pencil, normalized by one fixed free isomorphism. -/
def endpointHillNormalizedPencil (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  singularHillFreeInverse.comp
    (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) -
      z • singularHillDomainInclusion)

/-- The compact perturbation is identified with the physical potential and domain inclusion. -/
theorem endpointHillNormalizedPencil_sub_one (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    endpointHillNormalizedPencil r hr1 q z - 1 =
      singularHillFreeInverse.comp
        (hminusOneMultiplication (endpointHillHminusOne SpectralWeight.one r hr1 q) -
          (z+1) • singularHillDomainInclusion) := by
  apply ContinuousLinearMap.ext
  intro f
  change singularHillFreeInverse
    (singularHillLaplacian f + hminusOneMultiplication
      (endpointHillHminusOne SpectralWeight.one r hr1 q) f - z • singularHillDomainInclusion f) - f =
    singularHillFreeInverse (hminusOneMultiplication
      (endpointHillHminusOne SpectralWeight.one r hr1 q) f - (z+1) • singularHillDomainInclusion f)
  let a := singularHillLaplacian f
  let b := hminusOneMultiplication (endpointHillHminusOne SpectralWeight.one r hr1 q) f
  let c := singularHillDomainInclusion f
  have hID : singularHillFreeInverse (a+c) = f := singularHillFreeInverse_shift f
  calc
    _ = singularHillFreeInverse (a+b-z • c) - singularHillFreeInverse (a+c) := by rw [hID]
    _ = singularHillFreeInverse ((a+b-z • c)-(a+c)) := (map_sub _ _ _).symm
    _ = _ := by congr 1; rw [add_smul, one_smul]; abel

/-- Identity plus compact holds for every complex parameter, without a high-strip condition. -/
theorem isCompactOperator_endpointHillNormalizedPencil_sub_one (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    IsCompactOperator (endpointHillNormalizedPencil r hr1 q z - 1 :
      FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2) := by
  rw [endpointHillNormalizedPencil_sub_one]
  exact ((isCompactOperator_endpointH1Multiplication_physical r hr hr1 q).sub
    (isCompactOperator_singularHillDomainInclusion.smul (z+1))).clm_comp singularHillFreeInverse

/-- The full physical endpoint pencil has Fredholm index zero at every complex parameter. -/
theorem endpointHillNormalizedPencil_fredholm_index_zero (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    (endpointHillNormalizedPencil r hr1 q z).IsFredholm ∧
      Module.finrank ℂ (endpointHillNormalizedPencil r hr1 q z).ker =
        Module.finrank ℂ ((FourierLebesgueSpace (2:ℝ) 1 2) ⧸
          (endpointHillNormalizedPencil r hr1 q z).range) := by
  exact CompactSpectrum.fredholm_index_zero_of_compact_sub_smul _ (by norm_num : (1:ℂ) ≠ 0)
    (by simpa only [one_smul] using isCompactOperator_endpointHillNormalizedPencil_sub_one r hr hr1 q z)

/-- Injectivity gives full bijectivity, with arbitrary original H-minus-one right-hand sides. -/
theorem endpointHillNormalizedPencil_bijective_of_injective (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ)
    (hi : Function.Injective (endpointHillNormalizedPencil r hr1 q z)) :
    Function.Bijective (endpointHillNormalizedPencil r hr1 q z) :=
  CompactScalarPerturbation.bijective_of_injective _ (by norm_num : (1:ℂ) ≠ 0)
    (by simpa only [one_smul] using isCompactOperator_endpointHillNormalizedPencil_sub_one r hr hr1 q z) hi

/-- The normalized kernel is exactly the full original physical eigen-equation. -/
theorem endpointHillNormalizedPencil_apply_eq_zero_iff (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    endpointHillNormalizedPencil r hr1 q z f = 0 ↔
      singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
        z • singularHillDomainInclusion f := by
  constructor
  · intro h
    have he := congrArg singularHillFreeShift h
    change singularHillFreeShift (singularHillFreeInverse
      (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
        z • singularHillDomainInclusion f)) = singularHillFreeShift 0 at he
    rw [singularHillFreeShift_inverse, map_zero] at he
    exact sub_eq_zero.mp he
  · intro h
    change singularHillFreeInverse
      (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f -
        z • singularHillDomainInclusion f) = 0
    rw [h, sub_self, map_zero]

/-- Normalization preserves the exact physical eigenspace as a submodule of original H1. -/
theorem ker_endpointHillNormalizedPencil (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    (endpointHillNormalizedPencil r hr1 q z).ker =
      singularHillEigenspace (endpointHillHminusOne SpectralWeight.one r hr1 q) z := by
  ext f
  rw [mem_singularHillEigenspace_iff]
  exact endpointHillNormalizedPencil_apply_eq_zero_iff r hr1 q z f

/-- Every physical endpoint eigenspace is finite dimensional, at every complex parameter. -/
theorem finiteDimensional_endpointHillEigenspace (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    FiniteDimensional ℂ (singularHillEigenspace
      (endpointHillHminusOne SpectralWeight.one r hr1 q) z) := by
  rw [← ker_endpointHillNormalizedPencil]
  exact CompactScalarPerturbation.finiteDimensional_ker _ (by norm_num : (1:ℂ) ≠ 0)
    (by simpa only [one_smul] using isCompactOperator_endpointHillNormalizedPencil_sub_one r hr hr1 q z)

/-- Undoing the fixed normalization recovers the actual original operator pencil. -/
theorem endpointHillPencil_free_normalization (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) -
      z • singularHillDomainInclusion =
      singularHillFreeShift.comp (endpointHillNormalizedPencil r hr1 q z) := by
  apply ContinuousLinearMap.ext
  intro f
  exact (singularHillFreeShift_inverse _).symm

/-- Bijectivity of the normalization is equivalent to full physical pencil bijectivity. -/
theorem endpointHillPencil_bijective_iff_normalized (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    Function.Bijective (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) -
      z • singularHillDomainInclusion) ↔ Function.Bijective (endpointHillNormalizedPencil r hr1 q z) := by
  constructor
  · intro h
    exact singularHillFreeIsomorphism.symm.bijective.comp h
  · intro h
    rw [endpointHillPencil_free_normalization]
    exact singularHillFreeIsomorphism.bijective.comp h

/-- The normalized family is analytic in the spectral parameter on the entire complex plane. -/
theorem analyticAt_endpointHillNormalizedPencil_spectral (r : ℝ) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    AnalyticAt ℂ (endpointHillNormalizedPencil r hr1 q) z :=
  SchurComplement.analyticAt_compCLM analyticAt_const
    (analyticAt_const.sub (analyticAt_id.smul analyticAt_const))

/-- Every physical parameter has a local analytic Fredholm determinant, including singular ones. -/
theorem exists_local_endpointHillPencil_determinant (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∃ d : ℂ → ℂ,
      AnalyticOnNhd ℂ d U ∧ ∀ y ∈ U,
        Function.Bijective (singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) -
          y • singularHillDomainInclusion) ↔ d y ≠ 0 := by
  obtain ⟨U,hU,hz,d,hd,hcrit⟩ := CompactSpectrum.exists_local_analytic_determinant
    (analyticAt_endpointHillNormalizedPencil_spectral r hr1 q z) (by norm_num : (1:ℂ) ≠ 0)
    (by simpa only [one_smul] using isCompactOperator_endpointHillNormalizedPencil_sub_one r hr hr1 q z)
  refine ⟨U,hU,hz,d,hd,?_⟩
  intro y hy
  rw [endpointHillPencil_bijective_iff_normalized,
    ← ContinuousLinearMap.isUnit_iff_bijective]
  exact hcrit y hy

end NLS.KdV
