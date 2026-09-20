import NLS.ZakharovShabat.CanonicalDiscriminant
import NLS.ZakharovShabat.HilbertParityCompatibility

/-!
# The intrinsic Hilbert discriminant and all three spectral products

For every even Hilbert potential, the intrinsic discriminant also equals the
odd product minus two. Its squared characteristic function is the full product.
On continuous representatives it agrees with the actual monodromy trace.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The intrinsic Hilbert discriminant also comes from the odd product. -/
theorem canonicalDiscriminant_eq_odd_sub_two (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalDiscriminant (by simp) φ z = canonicalParityProduct (by simp) φ 1 z-2 :=
  canonicalParity_shifted_eq_hilbert φ hφ z

/-- The odd product is the intrinsic Hilbert discriminant plus two. -/
theorem canonicalOdd_eq_discriminant_add_two (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalParityProduct (by simp) φ 1 z = canonicalDiscriminant (by simp) φ z+2 := by
  rw [canonicalDiscriminant_eq_odd_sub_two φ hφ]
  ring

/-- The full product is the squared intrinsic discriminant minus four, for all even Hilbert potentials. -/
theorem canonicalPeriodic_eq_discriminant_sq_sub_four (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalPeriodicProduct (by simp) φ z = (canonicalDiscriminant (by simp) φ z)^2-4 := by
  rw [← canonicalParityProducts_mul (by simp) (by norm_num) φ hφ z,
    canonicalEven_eq_discriminant_sub_two, canonicalOdd_eq_discriminant_add_two φ hφ]
  ring

/-- On any compatible continuous representative the intrinsic function is the actual trace. -/
theorem canonicalDiscriminant_eq_classical (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    canonicalDiscriminant (by simp) φ z = classicalDiscriminant Φ z := by
  rw [canonicalDiscriminant, canonicalEven_eq_classical φ hφ Φ hΦ]
  ring

/-- Included Sobolev domain potentials recover the trace of their canonical representative. -/
theorem canonicalDiscriminant_domainInclusion (a : Domain 2)
    (ha : a ∈ domainParitySubspace 0) (z : ℂ) :
    canonicalDiscriminant (by simp) (domainInclusion a) z =
      classicalDiscriminant (physicalDomainCurve a) z :=
  canonicalDiscriminant_eq_classical _ ((mem_domainParitySubspace 0 a).mp ha) _
    (physicalBase_eq_extend_physicalDomainCurve a) z

/-- The zero-potential intrinsic Hilbert discriminant is exactly twice the cosine. -/
@[simp] theorem canonicalDiscriminant_zero (z : ℂ) :
    canonicalDiscriminant (by simp) (0 : PairSpace 2) z = freeDiscriminant z := by
  have h := canonicalDiscriminant_domainInclusion 0 (Submodule.zero_mem _) z
  simpa only [map_zero, physicalDomainCurve_zero, classicalDiscriminant_free] using h

/-- The even and odd Hilbert parity spectra are precisely the trace levels two and minus two. -/
theorem canonicalDiscriminant_parity_levels (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    (canonicalDiscriminant (by simp) φ z = 2 ↔ 0 < parityAlgebraicMultiplicity (by simp) φ 0 z) ∧
    (canonicalDiscriminant (by simp) φ z = -2 ↔ 0 < parityAlgebraicMultiplicity (by simp) φ 1 z) := by
  have he := ((canonicalParityProduct_spec (by simp) (by norm_num) φ hφ 0 (Or.inl rfl)).2 z).2
  have ho := ((canonicalParityProduct_spec (by simp) (by norm_num) φ hφ 1 (Or.inr rfl)).2 z).2
  rw [canonicalEven_eq_discriminant_sub_two, sub_eq_zero] at he
  rw [canonicalOdd_eq_discriminant_add_two φ hφ, add_eq_zero_iff_eq_neg] at ho
  exact ⟨he, ho⟩

/-- The full original periodic spectrum is exactly the intrinsic characteristic zero set. -/
theorem canonicalDiscriminant_sq_eq_four_iff (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    (canonicalDiscriminant (by simp) φ z)^2 = 4 ↔ z ∈ periodicSpectrum (by simp) φ := by
  have h := canonicalPeriodicProduct_eq_zero_iff (by simp) (by norm_num) φ z
  rw [canonicalPeriodic_eq_discriminant_sq_sub_four φ hφ, sub_eq_zero] at h
  exact h

end NLS.ZakharovShabat
