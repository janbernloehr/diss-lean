import NLS.Articles.KdVPseudomeasures.OriginalHillSpectrum
import NLS.KdV.HminusOnePhysicalCharacteristic

/-! The physical characteristic on the article's entire original real
H-minus-one domain. This identifies spectral zero sets, not their analytic
orders or physical algebraic multiplicities. -/
noncomputable section
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

/-- Raw unit-period coefficients of the entire original physical potential. -/
def originalPeriodOneCoefficients (q : OriginalHminusOnePotential) : PeriodOneHminusOne :=
  periodOneOriginalExtract q.val

/-- The realized coefficient model is the SAME original distribution on every smooth test. -/
theorem periodOneOriginal_originalPeriodOneCoefficients (q : OriginalHminusOnePotential) :
    periodOneOriginal (originalPeriodOneCoefficients q) = q.val :=
  periodOneOriginal_extract q.val q.property.2.2

/-- Reality of the coefficients follows from original distributional reality. -/
theorem originalPeriodOneCoefficients_real (q : OriginalHminusOnePotential) :
    IsRealPeriodOneHminusOne (originalPeriodOneCoefficients q) :=
  periodOneOriginalExtract_real q.val q.property.1

/-- The physical energy discriminant on the full original H-minus-one domain. -/
def originalHillDiscriminant (q : OriginalHminusOnePotential) (z : ℂ) : ℂ :=
  hillHminusDiscriminant (originalPeriodOneCoefficients q) z

/-- The ENTIRE original full-domain Hill spectrum is the physical
discriminant zero set for every original H-minus-one potential. -/
theorem original_spectrum_iff_HminusOne_discriminant
    (q : OriginalHminusOnePotential) (z : ℂ) :
    z ∈ singularHillSpectrum q.val ↔ originalHillDiscriminant q z ^ 2 = 4 := by
  rw [← periodOneOriginal_originalPeriodOneCoefficients q]
  exact singularHillSpectrum_periodOne_iff_discriminant (originalPeriodOneCoefficients q) z

end NLS.Articles.KdVPseudomeasures
