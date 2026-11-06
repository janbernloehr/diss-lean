import NLS.KdV.HillHminusSpectralDifferentials
import NLS.Fourier.ACPeriodicUnitCoefficients

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory NLS.LinearVolterra NLS.Fourier
namespace NLS.KdV

/-- At every native Hilbert source the genuine H-minus-one Gardner bracket
of the actual discriminants is the original physical derivative integral. -/
theorem hillHminusDiscriminants_Gardner_hilbert_integral
    (q : Coeff 2) (E F : ℂ) :
    NLS.Poisson.hminusGardnerBracket (fun r => hillHminusDiscriminant r E)
      (fun r => hillHminusDiscriminant r F) (NLS.Poisson.hilbertToHminus q)=
      ∫ x in (0 : ℝ)..1,
        NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve (hillNativeHilbertDirection q) E) x*
        NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientSpatialCurve (hillNativeHilbertDirection q) F) x := by
  have hp : NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve (hillNativeHilbertDirection q) F) 1=
      NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve (hillNativeHilbertDirection q) F) 0 := by
    dsimp only [NLS.LinearVolterra.extend]
    rw [projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num),hillEnergyDiscriminantGradientCurve,
      (hillDiscriminantGradientCurve_endpoints _ _).1,
      (hillDiscriminantGradientCurve_endpoints _ _).2]
  exact gardnerBivector_eq_integral_of_ac_coefficients _ _ _ _ _
    (continuous_extend _) (continuous_extend _) (continuous_extend _)
    (hillEnergyDiscriminantGradient_H1 _ _).1
    (ae_hasDerivAt_hillEnergyDiscriminantGradientCurve _ _) hp
    (hminusScalarGradient_hillDiscriminant_native_coefficients q E)
    (hminusScalarGradient_hillDiscriminant_native_coefficients q F)

/-- The actual extended discriminants commute at all native Hilbert sources,
without a reality or finite-gap hypothesis. -/
theorem hillHminusDiscriminants_Gardner_hilbert_zero
    (q : Coeff 2) (E F : ℂ) :
    NLS.Poisson.hminusGardnerBracket (fun r => hillHminusDiscriminant r E)
      (fun r => hillHminusDiscriminant r F) (NLS.Poisson.hilbertToHminus q)=0 := by
  rw [hillHminusDiscriminants_Gardner_hilbert_integral]
  have h := hillEnergyDiscriminantGardnerBracket_eq_zero (hillNativeHilbertDirection q) E F
  apply Eq.trans _ h
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillEnergyDiscriminantGradientCurve
    (hillNativeHilbertDirection q) F] with x hx
  rw [hx.deriv]

/-- The actual Hill discriminants Poisson commute at every complex H-minus-one
source and every pair of complex energies. Actual L2 density and continuity
of the genuine Gardner bracket extend the original physical identity. -/
theorem hillHminusDiscriminants_Gardner_commute (q : PeriodOneHminusOne) (E F : ℂ) :
    NLS.Poisson.hminusGardnerBracket (fun r => hillHminusDiscriminant r E)
      (fun r => hillHminusDiscriminant r F) q=0 := by
  have hE : AnalyticOnNhd ℂ (fun r => hillHminusDiscriminant r E) univ :=
    fun r _ => analyticAt_hillHminusDiscriminant_source r E
  have hF : AnalyticOnNhd ℂ (fun r => hillHminusDiscriminant r F) univ :=
    fun r _ => analyticAt_hillHminusDiscriminant_source r F
  have hc := (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _ hE hF).continuous
  have he := denseRange_periodOneL2Inclusion.equalizer hc continuous_const (by
    funext a
    change NLS.Poisson.hminusGardnerBracket _ _ (periodOneL2Inclusion a)=0
    rw [periodOneL2Inclusion_eq_hilbertToHminus]
    exact hillHminusDiscriminants_Gardner_hilbert_zero a E F)
  exact congrFun he q

end NLS.KdV
