import NLS.ZakharovShabat.ClassicalParityEigenvectors
import NLS.ZakharovShabat.CanonicalParityClassicalZeros

/-!
# Equality of original parity spectra and classical monodromy root sets

For even-supported Hilbert potentials admitting a continuous representative on
`[0,1]`, both directions of the eigenvector bridge identify the intrinsic even
and odd product zero sets with discriminant values two and minus two. These
are equalities of sets; classical determinant orders and entire normalization
still require separate proofs.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The classical parity characteristic determinant detects precisely positive original parity multiplicity. -/
theorem det_classicalMonodromy_eq_zero_iff_parityMultiplicity_pos
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (r : ℤ) (z : ℂ) :
    (classicalMonodromy Φ z-wave r 1 • 1).det = 0 ↔
      0 < parityAlgebraicMultiplicity (by simp) φ r z := by
  constructor
  · intro hz
    obtain ⟨v,hv,he⟩ := (det_classicalMonodromy_sub_scalar_eq_zero_iff Φ z (wave r 1)).mp hz
    exact (parityAlgebraicMultiplicity_pos_iff (by simp) φ hφ r z).mpr
      (exists_parity_eigenvector_of_classicalSolution φ hφ Φ hΦ z r v hv he)
  · exact det_classicalMonodromy_eq_zero_of_parityMultiplicity_pos φ hφ Φ hΦ r z

/-- Trace value two is equivalent to positive original even-sector algebraic multiplicity. -/
theorem classicalDiscriminant_eq_two_iff_evenMultiplicity_pos
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    classicalDiscriminant Φ z = 2 ↔ 0 < parityAlgebraicMultiplicity (by simp) φ 0 z := by
  constructor
  · intro hz
    obtain ⟨v,hv,he⟩ := (classicalDiscriminant_eq_two_iff Φ z).mp hz
    apply (parityAlgebraicMultiplicity_pos_iff (by simp) φ hφ 0 z).mpr
    exact exists_parity_eigenvector_of_classicalSolution φ hφ Φ hΦ z 0 v hv (by
      simpa only [wave_zero,one_smul] using he)
  · exact classicalDiscriminant_eq_two_of_evenMultiplicity_pos φ hφ Φ hΦ z

/-- Trace value minus two is equivalent to positive original odd-sector algebraic multiplicity. -/
theorem classicalDiscriminant_eq_neg_two_iff_oddMultiplicity_pos
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    classicalDiscriminant Φ z = -2 ↔ 0 < parityAlgebraicMultiplicity (by simp) φ 1 z := by
  constructor
  · intro hz
    obtain ⟨v,hv,he⟩ := (classicalDiscriminant_eq_neg_two_iff Φ z).mp hz
    apply (parityAlgebraicMultiplicity_pos_iff (by simp) φ hφ 1 z).mpr
    exact exists_parity_eigenvector_of_classicalSolution φ hφ Φ hΦ z 1 v hv (by
      have hw : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
      simpa only [hw,neg_one_smul] using he)
  · exact classicalDiscriminant_eq_neg_two_of_oddMultiplicity_pos φ hφ Φ hΦ z

/-- The intrinsic even-product zero set is exactly the classical trace-two set. -/
theorem canonicalEven_zero_iff_classicalDiscriminant_eq_two
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    canonicalParityProduct (by simp) φ 0 z = 0 ↔ classicalDiscriminant Φ z = 2 := by
  rw [((canonicalParityProduct_spec (by simp) (by norm_num) φ hφ 0 (Or.inl rfl)).2 z).2]
  exact (classicalDiscriminant_eq_two_iff_evenMultiplicity_pos φ hφ Φ hΦ z).symm

/-- The intrinsic odd-product zero set is exactly the classical trace-minus-two set. -/
theorem canonicalOdd_zero_iff_classicalDiscriminant_eq_neg_two
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    canonicalParityProduct (by simp) φ 1 z = 0 ↔ classicalDiscriminant Φ z = -2 := by
  rw [((canonicalParityProduct_spec (by simp) (by norm_num) φ hφ 1 (Or.inr rfl)).2 z).2]
  exact (classicalDiscriminant_eq_neg_two_iff_oddMultiplicity_pos φ hφ Φ hΦ z).symm

/-- The intrinsic full product and the classical discriminant squared minus four have exactly the same zeros. -/
theorem canonicalPeriodic_zero_iff_classicalDiscriminant_sq_sub_four_eq_zero
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    canonicalPeriodicProduct (by simp) φ z = 0 ↔ (classicalDiscriminant Φ z)^2-4 = 0 := by
  rw [← canonicalParityProducts_mul (by simp) (by norm_num) φ hφ z,mul_eq_zero,
    canonicalEven_zero_iff_classicalDiscriminant_eq_two φ hφ Φ hΦ z,
    canonicalOdd_zero_iff_classicalDiscriminant_eq_neg_two φ hφ Φ hΦ z]
  rw [show (classicalDiscriminant Φ z)^2-4 =
      (classicalDiscriminant Φ z-2)*(classicalDiscriminant Φ z+2) by ring,
    mul_eq_zero,sub_eq_zero,add_eq_zero_iff_eq_neg]

end NLS.ZakharovShabat
