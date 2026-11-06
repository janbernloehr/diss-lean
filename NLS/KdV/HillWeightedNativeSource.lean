import NLS.KdV.HillHminusOriginalSheets
import NLS.KdV.HillHminusPhysicalArnoldActions
import NLS.KdV.HillCanonicalGapBounds

/-! # The literal native weighted coefficients in the original rough Hill source -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

def hillWeightedNativeHminusSource (w : SpectralWeight) :
    WeightedCoeff w.doubleIndex.toWeight 2 →L[ℂ] PeriodOneHminusOne :=
  periodOneL2Inclusion.comp w.doubleIndex.toCoeff

@[simp] theorem hillWeightedNativeHminusSource_apply (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (k : ℤ) :
    (hillWeightedNativeHminusSource w q).val k = q.val k := by
  change (periodOneL2Inclusion (w.doubleIndex.toCoeff q)).val k = _
  rw [periodOneL2Inclusion_apply,SpectralWeight.toCoeff_apply]

theorem hillWeightedNativeHminusSource_real (w : SpectralWeight) (q : RealHillWeightedPotential w) :
    IsRealPeriodOneHminusOne (hillWeightedNativeHminusSource w q.val) := by
  intro k
  simp only [hillWeightedNativeHminusSource_apply]
  simpa only [SpectralWeight.toCoeff_apply] using q.property k

theorem hillWeightedNativeHminusSource_eq_original (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) :
    hillWeightedNativeHminusSource w q = hillOriginalHminusSource (hillPeriodOneUnitPotential w q) := by
  apply Subtype.ext
  funext k
  rw [hillWeightedNativeHminusSource_apply,hillOriginalHminusSource_apply]
  change q.val k = (hillForgetWeight w 2 (hillPeriodOnePotential w q)).val (2*k)
  rw [hillForgetWeight_apply,hillPeriodOnePotential_even]

def hillWeightedPhysicalSource (w : SpectralWeight) (q : RealHillWeightedPotential w) : RealPeriodOneHillPotential :=
  ⟨hillPeriodOneUnitPotential w q.val,hillPeriodOneUnitPotential_even w q.val,
    hillPeriodOneUnitPotential_real w q.val q.property⟩

theorem hillWeightedNative_ArnoldAction (w : SpectralWeight) (q : RealHillWeightedPotential w) (n : ℕ+) :
    hillHminusRealGapContourMoment (hillWeightedNativeHminusSource w q.val)
      (hillWeightedNativeHminusSource_real w q) n 0 = (hillPeriodOneAction w q.val q.property n : ℂ) := by
  have hh := hillHminusRealGapContourMoment_original_source (hillWeightedPhysicalSource w q) n 0
  simpa only [←hillWeightedNativeHminusSource_eq_original,hillWeightedPhysicalSource,hillPeriodOneAction] using! hh

end NLS.KdV
