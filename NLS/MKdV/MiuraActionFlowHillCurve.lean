import NLS.MKdV.MiuraActionFlowAbelianData
import NLS.MKdV.MiuraNativeActionFlowAllTimes

/-! # The actual native physical action orbit as a rough Hill curve -/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat NLS.KdV
open scoped ComplexConjugate
namespace NLS.MKdV

def miuraNativeHillActionCurve (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ)
    (t : ℝ) : RealPeriodOneHillPotential :=
  realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a j t).val)
    (miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a j t))

theorem continuous_miuraNativeHillActionCurve (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (j : ℕ) : Continuous (miuraNativeHillActionCurve s hs a j) :=
  continuous_realSobolevMiuraHillPotential_family _
    ((hierarchySobolevToScalarDomain s hs).continuous.comp (continuous_miuraActionFlow s a.val a.property j))
    (fun t => miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a j t))

theorem differentiableAt_miuraNativeHillActionCoefficients (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j) (t : ℝ) :
    DifferentiableAt ℝ (fun r => SpectralWeight.one.toCoeff (miuraNativeHillActionCurve s hs a j r).val) t := by
  let H := hierarchySobolevToScalarDomain s hs
  have hA := (H.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (hasDerivAt_miuraActionFlow_native s hs a j hj t)
  have hq := ((analyticAt_sobolevMiuraHillPotential (H (miuraNativeRealActionFlow s a j t).val)).differentiableAt.restrictScalars ℝ).comp t hA.differentiableAt
  simpa only [miuraNativeHillActionCurve,realSobolevMiuraHillPotential_toCoeff] using! hq

theorem miuraNativeHillActionCurve_labels (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (j : ℕ) (t0 t : ℝ) :
    hillRealLabels (miuraNativeHillActionCurve s hs a j t).val
      (miuraNativeHillActionCurve s hs a j t).property.1 (miuraNativeHillActionCurve s hs a j t).property.2 =
    hillRealLabels (miuraNativeHillActionCurve s hs a j t0).val
      (miuraNativeHillActionCurve s hs a j t0).property.1 (miuraNativeHillActionCurve s hs a j t0).property.2 :=
  (miuraNativeHillLabels_actionFlow s hs a j t).trans (miuraNativeHillLabels_actionFlow s hs a j t0).symm

end NLS.MKdV
