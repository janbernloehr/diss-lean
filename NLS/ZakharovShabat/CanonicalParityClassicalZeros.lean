import NLS.ZakharovShabat.PhysicalParityMonodromy
import NLS.ZakharovShabat.CanonicalParityProducts

/-!
# Original spectral-product zeros force classical discriminant values

For even-supported Hilbert potentials with a continuous representative on the
unit interval, the intrinsic even and odd zeros give trace values two and
minus two respectively. In particular the intrinsic parity factors cannot
vanish together. The converse, equality of multiplicities with classical
determinants, and the normalized entire-function identity are not asserted.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Positive original parity multiplicity forces the actual endpoint characteristic determinant to vanish. -/
theorem det_classicalMonodromy_eq_zero_of_parityMultiplicity_pos
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (r : ℤ) (z : ℂ)
    (hz : 0 < parityAlgebraicMultiplicity (by simp) φ r z) :
    (classicalMonodromy Φ z - wave r 1 • 1).det = 0 := by
  obtain ⟨a,hne,ha,he⟩ := (parityAlgebraicMultiplicity_pos_iff (by simp) φ hφ r z).mp hz
  rw [spectralPencil_apply,sub_eq_zero] at he
  exact det_classicalMonodromy_eq_zero_of_parity_eigenvector φ Φ hΦ a r ha hne z he.symm

/-- Original even-sector spectral points have classical discriminant value two. -/
theorem classicalDiscriminant_eq_two_of_evenMultiplicity_pos
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ)
    (hz : 0 < parityAlgebraicMultiplicity (by simp) φ 0 z) : classicalDiscriminant Φ z = 2 := by
  have h := det_classicalMonodromy_eq_zero_of_parityMultiplicity_pos φ hφ Φ hΦ 0 z hz
  simp only [wave_zero,one_smul] at h
  have hc := (classicalBoundaryDeterminants_compatible Φ z).1
  rw [h] at hc
  simpa only [neg_zero,zero_add] using hc.symm

/-- Original odd-sector spectral points have classical discriminant value minus two. -/
theorem classicalDiscriminant_eq_neg_two_of_oddMultiplicity_pos
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ)
    (hz : 0 < parityAlgebraicMultiplicity (by simp) φ 1 z) : classicalDiscriminant Φ z = -2 := by
  have h := det_classicalMonodromy_eq_zero_of_parityMultiplicity_pos φ hφ Φ hΦ 1 z hz
  have hw : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
  simp only [hw,neg_one_smul,sub_neg_eq_add] at h
  have hc := (classicalBoundaryDeterminants_compatible Φ z).2
  rw [h] at hc
  simpa only [zero_sub] using hc.symm

/-- A zero of the intrinsic even spectral product gives classical discriminant value two. -/
theorem classicalDiscriminant_eq_two_of_canonicalEven_zero
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ)
    (hz : canonicalParityProduct (by simp) φ 0 z = 0) : classicalDiscriminant Φ z = 2 :=
  classicalDiscriminant_eq_two_of_evenMultiplicity_pos φ hφ Φ hΦ z
    (((canonicalParityProduct_spec (by simp) (by norm_num) φ hφ 0 (Or.inl rfl)).2 z).2.mp hz)

/-- A zero of the intrinsic odd spectral product gives classical discriminant value minus two. -/
theorem classicalDiscriminant_eq_neg_two_of_canonicalOdd_zero
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ)
    (hz : canonicalParityProduct (by simp) φ 1 z = 0) : classicalDiscriminant Φ z = -2 :=
  classicalDiscriminant_eq_neg_two_of_oddMultiplicity_pos φ hφ Φ hΦ z
    (((canonicalParityProduct_spec (by simp) (by norm_num) φ hφ 1 (Or.inr rfl)).2 z).2.mp hz)

/-- The two intrinsic parity factors cannot vanish together for a continuously represented Hilbert potential. -/
theorem canonicalParityProducts_not_both_zero
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    ¬ (canonicalParityProduct (by simp) φ 0 z = 0 ∧ canonicalParityProduct (by simp) φ 1 z = 0) := by
  rintro ⟨he,ho⟩
  have h := (classicalDiscriminant_eq_two_of_canonicalEven_zero φ hφ Φ hΦ z he).symm.trans
    (classicalDiscriminant_eq_neg_two_of_canonicalOdd_zero φ hφ Φ hΦ z ho)
  norm_num at h

/-- Every intrinsic full-product zero is a zero of the classical discriminant squared minus four. -/
theorem classicalDiscriminant_sq_sub_four_eq_zero_of_canonicalPeriodic_zero
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ)
    (hz : canonicalPeriodicProduct (by simp) φ z = 0) : (classicalDiscriminant Φ z)^2 - 4 = 0 := by
  rw [← canonicalParityProducts_mul (by simp) (by norm_num) φ hφ z,mul_eq_zero] at hz
  rcases hz with he | ho
  · rw [classicalDiscriminant_eq_two_of_canonicalEven_zero φ hφ Φ hΦ z he]
    norm_num
  · rw [classicalDiscriminant_eq_neg_two_of_canonicalOdd_zero φ hφ Φ hΦ z ho]
    norm_num

end NLS.ZakharovShabat
