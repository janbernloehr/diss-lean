import NLS.Articles.KdVPseudomeasures.OriginalHminusOneDivisor
import NLS.KdV.HillHminusOneCanonicalRealLabels

/-!
# Canonical physical labels on the full original H-minus-one domain

No endpoint membership is assumed. These labels exhaust the actual full
physical spectrum and repeat each energy exactly its algebraic multiplicity.
On every endpoint realization they are the previously constructed labels.
-/
noncomputable section
open Set
open scoped Classical
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

/-- The entire original physical spectrum in its intrinsic ordered slots. -/
def originalHillLabels (q : OriginalHminusOnePotential) : ℕ → ℝ :=
  hillHminusLabels (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)

theorem monotone_originalHillLabels (q : OriginalHminusOnePotential) :
    Monotone (originalHillLabels q) :=
  monotone_hillHminusLabels (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)

/-- Every physical spectral point is listed, with no endpoint regularity premise. -/
theorem originalHillLabels_spectrum_iff (q : OriginalHminusOnePotential) (z : ℂ) :
    z ∈ singularHillSpectrum q.val ↔ ∃ j : ℕ, z = (originalHillLabels q j : ℂ) := by
  rw [original_spectrum_iff_HminusOne_discriminant,← sub_eq_zero]
  exact hillHminusLabels_roots_iff (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q) z

theorem originalHillLabels_finite_fiber (q : OriginalHminusOnePotential) (x : ℝ) :
    {j : ℕ | originalHillLabels q j = x}.Finite :=
  hillHminusLabels_finite_fiber (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) x

/-- Every repeated label counts an actual full-domain physical root vector. -/
theorem originalHillLabels_global_multiplicity (q : OriginalHminusOnePotential) (x : ℝ) :
    (∑ᶠ j : ℕ, if originalHillLabels q j = x then (1 : ℕ) else 0) =
      singularHillAlgebraicMultiplicity q.val x := by
  rw [originalHillLabels,hillHminusLabels_global_multiplicity]
  exact analyticOrderNatAt_originalHillDiscriminant q x

/-- The zero slot is an actual lowest physical spectral value. No simplicity
claim is needed for this statement. -/
theorem originalHillLabels_zero_lowest (q : OriginalHminusOnePotential) :
    (originalHillLabels q 0 : ℂ) ∈ singularHillSpectrum q.val ∧
      ∀ z ∈ singularHillSpectrum q.val, originalHillLabels q 0 ≤ z.re := by
  refine ⟨(originalHillLabels_spectrum_iff q _).mpr ⟨0,rfl⟩,?_⟩
  intro z hz
  obtain ⟨j,rfl⟩ := (originalHillLabels_spectrum_iff q z).mp hz
  exact monotone_originalHillLabels q (Nat.zero_le j)

/-- The complete ordered physical list determines the original isospectral
set, on its entire H-minus-one domain. -/
theorem mem_originalIsospectralSet_iff_originalHillLabels (q p : OriginalHminusOnePotential) :
    p ∈ originalIsospectralSet q ↔ originalHillLabels p = originalHillLabels q := by
  constructor
  · intro h
    apply NLS.ordered_nat_enumeration_eq_of_multiplicity _ _
      (originalHillLabels_finite_fiber p) (originalHillLabels_finite_fiber q)
      (monotone_originalHillLabels p) (monotone_originalHillLabels q)
    intro x
    rw [originalHillLabels_global_multiplicity,originalHillLabels_global_multiplicity,h x]
  · intro h z
    by_cases hz : z.im = 0
    · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
      rw [he,← originalHillLabels_global_multiplicity,← originalHillLabels_global_multiplicity,h]
    · rw [singularHillAlgebraicMultiplicity_eq_zero_of_im_ne_zero p.val p.property.1 z hz,
        singularHillAlgebraicMultiplicity_eq_zero_of_im_ne_zero q.val q.property.1 z hz]

/-- Every endpoint order gives the same full original physical labels. -/
theorem originalHillLabels_sourceOriginalPotential (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) :
    originalHillLabels (sourceOriginalPotential r hr q) = sourceHillLabels r hr q := by
  apply NLS.ordered_nat_enumeration_eq_of_multiplicity _ _
    (originalHillLabels_finite_fiber _) (sourceHillLabels_finite_fiber r hr q)
    (monotone_originalHillLabels _) (monotone_sourceHillLabels r hr q)
  intro x
  rw [originalHillLabels_global_multiplicity,sourceHillLabels_global_multiplicity,
    sourceHillAlgebraicMultiplicity_eq_original]
  rfl

/-- Full original physical gaps, evenly extended to signed indices with zero at zero. -/
def originalCanonicalGapValues (q : OriginalHminusOnePotential) (k : ℤ) : ℂ :=
  if k = 0 then 0 else
    ((originalHillLabels q (2*k.natAbs)-originalHillLabels q (2*k.natAbs-1) : ℝ) : ℂ)

@[simp] theorem originalCanonicalGapValues_zero (q : OriginalHminusOnePotential) :
    originalCanonicalGapValues q 0 = 0 := by simp [originalCanonicalGapValues]

theorem originalCanonicalGapValues_neg (q : OriginalHminusOnePotential) (k : ℤ) :
    originalCanonicalGapValues q (-k) = originalCanonicalGapValues q k := by
  simp only [originalCanonicalGapValues,neg_eq_zero,Int.natAbs_neg]

theorem originalCanonicalGapValues_im (q : OriginalHminusOnePotential) (k : ℤ) :
    (originalCanonicalGapValues q k).im = 0 := by
  unfold originalCanonicalGapValues
  split_ifs <;> rfl

theorem originalCanonicalGapValues_isospectral (q p : OriginalHminusOnePotential)
    (h : p ∈ originalIsospectralSet q) : originalCanonicalGapValues p = originalCanonicalGapValues q := by
  have he := (mem_originalIsospectralSet_iff_originalHillLabels q p).mp h
  funext k
  simp only [originalCanonicalGapValues,he]

/-- The original gap sequence agrees exactly with the endpoint sequence,
including all central slots, without a changed normalization. -/
theorem originalCanonicalGapValues_sourceOriginalPotential (r : ℝ)
    (hr : AdmissiblePredualOrder r) (q : Potential r) :
    originalCanonicalGapValues (sourceOriginalPotential r hr q) = sourceCanonicalGapValues r hr q := by
  funext k
  simp only [originalCanonicalGapValues,sourceCanonicalGapValues,originalHillLabels_sourceOriginalPotential]

end NLS.Articles.KdVPseudomeasures
