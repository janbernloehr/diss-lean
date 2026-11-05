import NLS.KdV.HillPeriodOneRestriction

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Even-index restriction is the actual inverse of the physical period-one
insertion on its original even source subspace. -/
theorem hillPeriodOnePotential_restriction_even (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (hq : w.toCoeff q∈Coeff.paritySubspace 0) :
    hillPeriodOnePotential w (hillPeriodOneRestriction w q)=q := by
  have he := hillPeriodOneCoefficientMap_restriction_even w q hq
  change w.toCoeff (hillPeriodOnePotential w (hillPeriodOneRestriction w q))=w.toCoeff q at he
  apply Subtype.ext
  funext k
  simpa only [SpectralWeight.toCoeff_apply] using congrArg (fun a : Coeff 2 => a k) he

/-- The restriction loses no physical source norm on even coefficients. -/
theorem norm_hillPeriodOneRestriction_even (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (hq : w.toCoeff q∈Coeff.paritySubspace 0) :
    ‖hillPeriodOneRestriction w q‖=‖q‖ := by
  rw [←norm_hillPeriodOnePotential w (hillPeriodOneRestriction w q),hillPeriodOnePotential_restriction_even w q hq]

/-- The unit-weight physical adapter returns the literal original even source. -/
theorem hillPeriodOneUnitPotential_restriction_even
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) :
    hillPeriodOneUnitPotential SpectralWeight.one (hillPeriodOneRestriction SpectralWeight.one q)=q := by
  have he := hillPeriodOneCoefficientMap_restriction_even SpectralWeight.one q hq
  rw [hillPeriodOneCoefficientMap_eq_unit] at he
  apply Subtype.ext
  funext k
  simpa only [SpectralWeight.toCoeff_apply] using congrArg (fun a : Coeff 2 => a k) he

/-- Original Fourier reality is preserved by even-index restriction. -/
theorem hillPeriodOneRestriction_real (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (hr : IsRealHillPotential (w.toCoeff q)) :
    IsRealHillPotential (w.doubleIndex.toCoeff (hillPeriodOneRestriction w q)) := by
  intro k
  simpa only [SpectralWeight.toCoeff_apply,hillPeriodOneRestriction_apply,mul_neg] using hr (2*k)

end NLS.KdV
