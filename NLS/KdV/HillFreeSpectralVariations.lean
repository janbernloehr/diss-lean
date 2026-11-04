import NLS.KdV.HillFreeDirichlet
import NLS.KdV.HillDirichletSlopeVariation
import NLS.KdV.HillWeakHamiltonianUniqueness
import NLS.KdV.ClassicalHillDuhamel
/-! # Actual free Hill states and trace stationarity on mean-zero tangents -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.Fourier
namespace NLS.KdV

theorem classicalHillFlow_free_cosine (z : ℂ) (t : Icc (0:ℝ) 1) :
    classicalHillFlow 0 (z^2) (1,0) t=(cos (z*t.val),-z*sin (z*t.val)) := by
  apply Eq.symm
  apply solution_unique (classicalHillCoefficientCurve 0 (z^2)) (1,0)
    (fun x : ℝ => (cos (z*x),-z*sin (z*x))) (by fun_prop) (by simp) _ t.property
  intro s _
  have harg : HasDerivAt (fun w : ℂ => z*w) z (s.val:ℂ) := by
    convert! (hasDerivAt_id (s.val:ℂ)).const_mul z using 1
    ring
  have hcos := harg.ccos.comp_ofReal
  have hsin := (harg.csin.const_mul (-z)).comp_ofReal
  change HasDerivAt (fun x : ℝ => (cos (z*x),-z*sin (z*x)))
    (-z*sin (z*s.val),(0-z^2)*cos (z*s.val)) s.val
  convert! hcos.prodMk hsin using 1
  ring

private theorem hillL2FrequencyStateCurve_free_eq_classical (z : ℂ) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    hillL2FrequencyStateCurve 0 z v t=classicalHillFlow 0 (z^2) v t := by
  have he : SpectralWeight.one.toCoeff (hillContinuousCoefficients (0 : C(AddCircle (2:ℝ),ℂ)))=(0 : Coeff 2) := by
    ext k
    simpa only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,Fourier.continuousFourierCLM_apply] using
      congrArg (fun f : Coeff 2 => f k) (map_zero Fourier.continuousFourierCLM)
  rw [← he,hillL2FrequencyStateCurve_eq_classical]
  rfl

theorem hillL2FrequencyStateCurve_free_cosine (z : ℂ) (t : Icc (0:ℝ) 1) :
    hillL2FrequencyStateCurve 0 z (1,0) t=(cos (z*t.val),-z*sin (z*t.val)) := by
  rw [hillL2FrequencyStateCurve_free_eq_classical,classicalHillFlow_free_cosine]

theorem hillL2FrequencyStateCurve_free_sine (z : ℂ) (hz : z≠0) (t : Icc (0:ℝ) 1) :
    hillL2FrequencyStateCurve 0 z (0,1) t=(sin (z*t.val)/z,cos (z*t.val)) := by
  rw [hillL2FrequencyStateCurve_free_eq_classical,classicalHillFlow_free_sine z hz]

theorem hillL2FrequencyStateCurve_free_sine_zero (t : Icc (0:ℝ) 1) :
    hillL2FrequencyStateCurve 0 0 (0,1) t=((t.val:ℂ),1) := by
  rw [hillL2FrequencyStateCurve_free_eq_classical,zero_pow (by norm_num : (2:ℕ)≠0),classicalHillFlow_free_zero]

theorem hillL2TraceGradientCurve_free (z : ℂ) (hz : z≠0) (t : Icc (0:ℝ) 1) :
    hillL2TraceGradientCurve 0 z t=sin z/z := by
  rw [hillL2TraceGradientCurve_apply,hillL2FrequencyStateCurve_free_cosine,
    hillL2FrequencyStateCurve_free_sine z hz,hillL2FrequencyStateCurve_free_cosine,
    hillL2FrequencyStateCurve_free_sine z hz]
  dsimp only [Prod.fst,Prod.snd]
  simp only [ofReal_one,mul_one,sub_self,zero_mul]
  calc
    _ = (sin z/z)*(sin (z*t.val)^2+cos (z*t.val)^2) := by field_simp;ring
    _ = _ := by rw [sin_sq_add_cos_sq,mul_one]

theorem hillL2TraceGradientCurve_free_zero (t : Icc (0:ℝ) 1) :
    hillL2TraceGradientCurve 0 0 t=1 := by
  rw [hillL2TraceGradientCurve_apply,hillL2FrequencyStateCurve_free_cosine,
    hillL2FrequencyStateCurve_free_sine_zero,hillL2FrequencyStateCurve_free_cosine,
    hillL2FrequencyStateCurve_free_sine_zero]
  simp

theorem fderiv_hillL2Discriminant_free_of_mean_zero (h : Coeff 2)
    (hmean : (∫ x in (0:ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x)=0) (E : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) 0) h=0 := by
  rw [fderiv_hillL2Discriminant_eq_traceGradient_integral]
  by_cases hz : Complex.sqrt E=0
  · simp only [hz,NLS.LinearVolterra.extend,hillL2TraceGradientCurve_free_zero,mul_one]
    exact hmean
  · simp only [NLS.LinearVolterra.extend,hillL2TraceGradientCurve_free _ hz]
    rw [intervalIntegral.integral_mul_const,hmean,zero_mul]

theorem hillL2DirichletSlope_free (E : ℂ) :
    hillL2DirichletSlope 0 E=cos (Complex.sqrt E) := by
  change (hillL2FrequencyStateCurve 0 (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2=_
  by_cases hz : Complex.sqrt E=0
  · rw [hz,hillL2FrequencyStateCurve_free_sine_zero]
    simp
  · rw [hillL2FrequencyStateCurve_free_sine _ hz]
    simp

theorem hillDirichletSheetRoot_free (E : ℂ) : hillDirichletSheetRoot 0 E=0 := by
  rw [hillDirichletSheetRoot,hillL2DirichletSlope_free,hillL2Discriminant_zero]
  ring

theorem integral_hillPhysicalDirection_eq_zero_of_even (h : Coeff 2)
    (hh : h∈Coeff.paritySubspace 0) (hm : h 0=0) :
    (∫ x in (0:ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x)=0 := by
  have hp := hillPhysicalCurvePairing_unitWaveCurve_even h hh 0
  rw [hillPhysicalCurvePairing_apply] at hp
  simpa [NLS.LinearVolterra.extend,unitWaveCurve,wave,hm] using hp
end NLS.KdV
