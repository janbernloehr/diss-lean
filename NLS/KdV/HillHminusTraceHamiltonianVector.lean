import NLS.KdV.HillHminusSpectralDifferentials
import NLS.KdV.HillClosedCurveSourceCoefficients
import NLS.KdV.HillIndexedDiscriminantSources
import NLS.Poisson.GardnerHamiltonianTransport

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra
namespace NLS.KdV

/-- The actual trace gradient at EVERY original even source has the
literal original unit Fourier coefficients, with no native replacement. -/
theorem hillHminusDiscriminant_original_gradient_coefficients
    (q : RealPeriodOneHillPotential) (E : ℂ) (k : ℤ) :
    (NLS.Poisson.hminusScalarGradient (fun a => hillHminusDiscriminant a E)
        (hillOriginalHminusSource q.val)).val k =
      Fourier.unitFourierCoefficient (NLS.LinearVolterra.extend
        (hillEnergyDiscriminantGradientCurve (SpectralWeight.one.toCoeff q.val) E)) k := by
  let v := SpectralWeight.one.doubleIndex.toCoeff (hillPeriodOneRestriction SpectralWeight.one q.val)
  have hs : NLS.Poisson.hilbertToHminus v = hillOriginalHminusSource q.val := by
    rw [←periodOneL2Inclusion_eq_hilbertToHminus]
    rfl
  have hv : hillNativeHilbertDirection v = SpectralWeight.one.toCoeff q.val := by
    rw [hillNativeHilbertDirection_eq_periodDouble]
    exact periodDouble_hillPeriodOneRestriction_even q.val q.property.1
  simpa only [hs,hv] using hminusScalarGradient_hillDiscriminant_native_coefficients v E k

/-- The genuine fixed-energy trace Hamiltonian vector is the NEGATIVE of
the actual physical trace source, at every complex energy and original
real even L2 source. The source energy is held fixed in this derivative. -/
theorem hillHminusDiscriminant_HamiltonianVector_eq_neg_source
    (q : RealPeriodOneHillPotential) (E : ℂ) :
    NLS.Poisson.gardnerHamiltonianVector (fun a => hillHminusDiscriminant a E)
        (hillOriginalHminusSource q.val) =
      -hillOriginalHminusSource (hillEnergyHamiltonianSource (SpectralWeight.one.toCoeff q.val) E) := by
  let p := SpectralWeight.one.toCoeff q.val
  let f := hillEnergyDiscriminantGradientCurve p E
  let g := hillEnergyDiscriminantGradientSpatialCurve p E
  have hp : NLS.LinearVolterra.extend f 1 = NLS.LinearVolterra.extend f 0 := by
    dsimp only [NLS.LinearVolterra.extend]
    rw [projIcc_of_mem _ (show (1:ℝ) ∈ Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 1 by norm_num)]
    exact ((hillDiscriminantGradientCurve_endpoints p (Complex.sqrt E)).2.trans
      (hillDiscriminantGradientCurve_endpoints p (Complex.sqrt E)).1.symm)
  have hd := Fourier.unitFourierCoefficient_ac_periodic_prescribed_derivative
    (NLS.LinearVolterra.extend f) (NLS.LinearVolterra.extend g)
    (hillEnergyDiscriminantGradient_H1 p E).1 (continuous_extend g)
    (ae_hasDerivAt_hillEnergyDiscriminantGradientCurve p E) hp
  apply Subtype.ext
  funext k
  change (NLS.Poisson.gardnerHamiltonianVector (fun a => hillHminusDiscriminant a E)
      (hillOriginalHminusSource q.val)).val k =
    -(hillOriginalHminusSource (hillEnergyHamiltonianSource p E)).val k
  rw [NLS.Poisson.gardnerHamiltonianVector_apply,hillHminusDiscriminant_original_gradient_coefficients]
  change (2 * Real.pi : ℂ) * I * k * Fourier.unitFourierCoefficient (NLS.LinearVolterra.extend f) k = _
  calc
    _ = Fourier.unitFourierCoefficient (NLS.LinearVolterra.extend g) k := by
      rw [hd k]
      ring
    _ = _ := by
      unfold hillEnergyHamiltonianSource
      rw [hillOriginalHminusSource_closedCurve_apply]
      simp only [g,Fourier.unitFourierCoefficient,NLS.LinearVolterra.extend,
        ContinuousMap.neg_apply,neg_mul,intervalIntegral.integral_neg,neg_neg]

end NLS.KdV
