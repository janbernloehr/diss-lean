import NLS.KdV.HillL2TraceGradients
import NLS.KdV.ClassicalHillGardnerTraceInvolution
import NLS.FunctionalAnalysis.UnitComplexCurveIntegral

/-! # Actual Gardner trace involution at complex L2 Hill potentials

Norm-continuous physical gradient curves transfer the actual scalar
continuous-potential identities through finite Fourier synthesis. No
periodic source regularity or differentiability of the potential is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
namespace NLS.KdV

private theorem trace_pairing_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (z w : ℂ) :
    unitComplexCurveIntegral
      (hillL2TraceGradientCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z*
        hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w)=
    ∫ x in (0 : ℝ)..1,classicalHillTracePairingKernel (hillUnitPotentialCurve Q) (z^2) x*
      classicalHillTracePairingKernelDx (hillUnitPotentialCurve Q) (w^2) x := by
  rw [unitComplexCurveIntegral_apply]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x∈Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',ContinuousMap.mul_apply,
    hillL2TraceGradientCurve_eq_classical,hillL2TraceGradientSpatialCurve_eq_classical]

/-- The scalar Gardner pairing of actual rough trace gradients vanishes at all energies. -/
theorem integral_hillL2TraceGradient_mul_spatial_eq_zero (q : Coeff 2) (z w : ℂ) :
    (∫ x in (0 : ℝ)..1,extend (hillL2TraceGradientCurve q z) x*
      extend (hillL2TraceGradientSpatialCurve q w) x)=0 := by
  let F (p : Coeff 2) := unitComplexCurveIntegral
    (hillL2TraceGradientCurve p z*hillL2TraceGradientSpatialCurve p w)
  have hF : Continuous F := unitComplexCurveIntegral.continuous.comp
    ((continuous_hillL2TraceGradientCurve z).mul (continuous_hillL2TraceGradientSpatialCurve w))
  have hf (a : ℤ →₀ ℂ) : F (Coeff.ofFinsupp a)=0 := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have he : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    dsimp only [F]
    rw [← he,trace_pairing_eq_classical]
    exact integral_classicalHillTracePairingKernel_mul_Dx_eq_zero (hillUnitPotentialCurve Q) (z^2) (w^2)
  have he : F=(fun _ : Coeff 2 => (0 : ℂ)) :=
    (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer hF continuous_const (funext hf)
  exact congrFun he q

/-- The same identity with the actual spatial `deriv` of the rough gradient. -/
theorem integral_hillL2TraceGradient_mul_deriv_eq_zero (q : Coeff 2) (z w : ℂ) :
    (∫ x in (0 : ℝ)..1,extend (hillL2TraceGradientCurve q z) x*
      deriv (extend (hillL2TraceGradientCurve q w)) x)=0 := by
  have he : (∫ x in (0 : ℝ)..1,extend (hillL2TraceGradientCurve q z) x*
      deriv (extend (hillL2TraceGradientCurve q w)) x)=
      ∫ x in (0 : ℝ)..1,extend (hillL2TraceGradientCurve q z) x*
        extend (hillL2TraceGradientSpatialCurve q w) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
    filter_upwards [ae_hasDerivAt_hillL2TraceGradientCurve q w] with x hx
    rw [hx.deriv]
  rw [he]
  exact integral_hillL2TraceGradient_mul_spatial_eq_zero q z w

/-- Matching endpoint values of the actual rough spatial trace gradient. -/
theorem hillL2TraceGradientSpatialCurve_endpoints (q : Coeff 2) (z : ℂ) :
    hillL2TraceGradientSpatialCurve q z ⟨1,by norm_num⟩=
      hillL2TraceGradientSpatialCurve q z ⟨0,by norm_num⟩ := by
  let F (p : Coeff 2) := hillL2TraceGradientSpatialCurve p z ⟨1,by norm_num⟩
  let G (p : Coeff 2) := hillL2TraceGradientSpatialCurve p z ⟨0,by norm_num⟩
  have hF : Continuous F := (continuous_eval_const _).comp (continuous_hillL2TraceGradientSpatialCurve z)
  have hG : Continuous G := (continuous_eval_const _).comp (continuous_hillL2TraceGradientSpatialCurve z)
  have hf (a : ℤ →₀ ℂ) : F (Coeff.ofFinsupp a)=G (Coeff.ofFinsupp a) := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have he : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    dsimp only [F,G]
    rw [← he,hillL2TraceGradientSpatialCurve_eq_classical,hillL2TraceGradientSpatialCurve_eq_classical]
    exact classicalHillTracePairingKernelDx_endpoints (hillUnitPotentialCurve Q) (z^2)
  exact congrFun ((Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer hF hG (funext hf)) q

/-- The actual rough trace-gradient derivative has zero physical mean. -/
theorem integral_hillL2TraceGradientSpatialCurve_eq_zero (q : Coeff 2) (z : ℂ) :
    (∫ x in (0 : ℝ)..1,extend (hillL2TraceGradientSpatialCurve q z) x)=0 := by
  let F (p : Coeff 2) := unitComplexCurveIntegral (hillL2TraceGradientSpatialCurve p z)
  have hF : Continuous F := unitComplexCurveIntegral.continuous.comp
    (continuous_hillL2TraceGradientSpatialCurve z)
  have hf (a : ℤ →₀ ℂ) : F (Coeff.ofFinsupp a)=0 := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    have he : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=Coeff.ofFinsupp (p := 2) a := by
      ext k
      simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    have hi : F (Coeff.ofFinsupp a)=∫ x in (0 : ℝ)..1,
        extend (classicalHillDiscriminantGardnerDirection (hillUnitPotentialCurve Q) (z^2)) x := by
      dsimp only [F]
      rw [← he,unitComplexCurveIntegral_apply]
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x∈Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using hx
      simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx',
        hillL2TraceGradientSpatialCurve_eq_classical,classicalHillDiscriminantGardnerDirection,
        ContinuousMap.coe_mk]
    rw [hi]
    exact integral_classicalHillDiscriminantGardnerDirection_eq_zero (hillUnitPotentialCurve Q) (z^2)
  exact congrFun ((Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer hF continuous_const (funext hf)) q

end NLS.KdV
