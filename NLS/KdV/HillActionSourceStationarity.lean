import NLS.KdV.HillContourHamiltonianSources

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Every physical moment is stationary in each genuine contour Hamiltonian source. -/
theorem hillRealSourceMoment_contourHamiltonianSource_fderiv
    (n : ℕ) (hn : 1≤n) (m : ℕ) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hR : 0≤r) (ha : ContinuousOn a (sphere c r)) :
    (fderiv ℂ (hillRealSourceMoment q hq hr n m) (SpectralWeight.one.toCoeff q))
      (SpectralWeight.one.toCoeff (hillEnergyContourHamiltonianSource (SpectralWeight.one.toCoeff q) a c r hR ha))=0 := by
  rw [hillRealSourceMoment_gradient q hq hr n hn m,hillEnergyContourHamiltonianSource_pairing]
  have hz := unitComplexCurvePairing_hillEnergyGradientContour_eq_zero (SpectralWeight.one.toCoeff q)
    (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q) m) a
    (hillRealGapCenter q hq hr n : ℂ) c
    (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n) r
    (add_nonneg (hillRealGapContour_geometry q hq hr n hn).1
      (hillRealGapContour_geometry q hq hr n hn).2.1.le) hR
    (continuousOn_hillPhysicalMomentGradientWeight q hq hr n hn m) ha
  have hc : unitComplexCurvePairing
      (hillEnergyGradientSpatialContour (SpectralWeight.one.toCoeff q) a c r)
      (hillPhysicalMomentGradient q hq hr n m)=0 := by
    rw [unitComplexCurvePairing_apply]
    simp_rw [mul_comm]
    exact hz
  exact neg_eq_zero.mpr hc

/-- The source derivatives of all actual physical moments commute. -/
theorem hillRealSourceMoment_physicalMomentHamiltonianSource_fderiv
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (m l : ℕ) :
    (fderiv ℂ (hillRealSourceMoment q hq hr n m) (SpectralWeight.one.toCoeff q))
      (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q hq hr k hk l))=0 :=
  hillRealSourceMoment_contourHamiltonianSource_fderiv q hq hr n hn m _ _ _ _ _

end NLS.KdV
