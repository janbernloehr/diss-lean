import NLS.KdV.HillClosedCurveDirections
import NLS.KdV.HillIsospectralGradientContours
import NLS.KdV.HillPhysicalActionGradients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual negative spatial gradient of a physical contour,
realized as a mean-zero period-one coefficient source. -/
def hillEnergyContourHamiltonianSource (p : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) : WeightedCoeff SpectralWeight.one.toWeight 2 :=
  hillClosedCurveCoefficients (-(hillEnergyGradientSpatialContour p a c r))
    (congrArg Neg.neg (hillEnergyGradientContours_closed p a c r hr ha).2)

theorem hillEnergyContourHamiltonianSource_mem_even (p : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) :
    SpectralWeight.one.toCoeff (hillEnergyContourHamiltonianSource p a c r hr ha)∈Coeff.paritySubspace 0 :=
  hillClosedCurveCoefficients_mem_even _ _

theorem hillEnergyContourHamiltonianSource_mean_zero (p : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) :
    (hillEnergyContourHamiltonianSource p a c r hr ha).val 0=0 := by
  rw [hillEnergyContourHamiltonianSource,hillClosedCurveCoefficients_zero]
  change (∫ x in (0 : ℝ)..1,-NLS.LinearVolterra.extend (hillEnergyGradientSpatialContour p a c r) x)=0
  rw [intervalIntegral.integral_neg,hillEnergyGradientSpatialContour_integral_eq_zero p a c r hr ha,neg_zero]

theorem hillEnergyContourHamiltonianSource_pairing (p : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) (v : Curve ℂ) :
    hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff (hillEnergyContourHamiltonianSource p a c r hr ha)) v=
      -unitComplexCurvePairing (hillEnergyGradientSpatialContour p a c r) v := by
  rw [hillEnergyContourHamiltonianSource,hillClosedCurveCoefficients_pairing]
  exact map_neg (unitComplexCurvePairing.flip v) (hillEnergyGradientSpatialContour p a c r)

/-- Every energy discriminant is stationary in this genuine physical
source direction. This is an actual coefficient Frechet derivative. -/
theorem hillEnergyContourHamiltonianSource_isospectral (p : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) (energy : ℂ) :
    (fderiv ℂ (fun q : Coeff 2 => hillL2Discriminant q energy) p)
      (SpectralWeight.one.toCoeff (hillEnergyContourHamiltonianSource p a c r hr ha))=0 := by
  rw [hillEnergyDiscriminantGradient_represents_potential,hillEnergyContourHamiltonianSource_pairing]
  have hcomm : unitComplexCurvePairing (hillEnergyGradientSpatialContour p a c r)
      (hillEnergyDiscriminantGradientCurve p energy)=
      unitComplexCurvePairing (hillEnergyDiscriminantGradientCurve p energy)
        (hillEnergyGradientSpatialContour p a c r) := by
    rw [unitComplexCurvePairing_apply,unitComplexCurvePairing_apply,mul_comm]
  rw [hcomm,unitComplexCurvePairing_energy_spatialContour_eq_zero p a c r hr ha energy,neg_zero]

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillPhysicalMomentHamiltonianSource (n : ℕ) (hn : 1≤n) (m : ℕ) :
    WeightedCoeff SpectralWeight.one.toWeight 2 :=
  hillEnergyContourHamiltonianSource (SpectralWeight.one.toCoeff q)
    (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q) m)
    (hillRealGapCenter q hq hr n : ℂ) (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)
    (add_nonneg (hillRealGapContour_geometry q hq hr n hn).1 (hillRealGapContour_geometry q hq hr n hn).2.1.le)
    (continuousOn_hillPhysicalMomentGradientWeight q hq hr n hn m)

theorem hillPhysicalMomentHamiltonianSource_isospectral (n : ℕ) (hn : 1≤n) (m : ℕ) (energy : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p energy) (SpectralWeight.one.toCoeff q))
      (SpectralWeight.one.toCoeff (hillPhysicalMomentHamiltonianSource q hq hr n hn m))=0 :=
  hillEnergyContourHamiltonianSource_isospectral _ _ _ _ _ _ energy

end NLS.KdV
