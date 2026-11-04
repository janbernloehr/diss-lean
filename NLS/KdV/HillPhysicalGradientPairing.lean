import NLS.KdV.HillActionSourceVariation
import NLS.KdV.HillDirichletGradientCurves

/-! # Physical gradient pairings for the actual Hill trace

The actual rough trace gradient is absolutely continuous with its proved
spatial derivative and matching endpoints. Periodic integration by parts
and the actual Fourier realization identify its weak physical pairings.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ComplexAnalysis NLS.Fourier
namespace NLS.KdV

theorem absolutelyContinuousOnInterval_hillL2TraceGradientCurve (q : Coeff 2) (z : ℂ) :
    AbsolutelyContinuousOnInterval (extend (hillL2TraceGradientCurve q z)) 0 1 := by
  let C := hillL2FrequencyStateCurve q z (1,0)
  let S := hillL2FrequencyStateCurve q z (0,1)
  let e : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  have hC := absolutelyContinuousOnInterval_clm
    (absolutelyContinuousOnInterval_hillStateCurve q z (1,0)) (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hS := absolutelyContinuousOnInterval_clm
    (absolutelyContinuousOnInterval_hillStateCurve q z (0,1)) (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hh := (((hC.smul hC).const_smul (S e).1).add
    ((hC.smul hS).const_smul ((S e).2-(C e).1))).sub ((hS.smul hS).const_smul (C e).2)
  convert! hh using 1
  funext x
  simp only [NLS.LinearVolterra.extend,hillL2TraceGradientCurve_apply,
    Pi.add_apply,Pi.sub_apply,smul_eq_mul]
  simp only [Pi.mul_apply,ContinuousLinearMap.coe_fst']
  dsimp only [C,S,e]
  ring

theorem intervalIntegrable_deriv_hillL2TraceGradientCurve (q : Coeff 2) (z : ℂ) :
    IntervalIntegrable (deriv (extend (hillL2TraceGradientCurve q z))) volume 0 1 := by
  apply ((continuous_extend (hillL2TraceGradientSpatialCurve q z)).intervalIntegrable 0 1).congr_ae
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillL2TraceGradientCurve q z] with x hx
  exact hx.deriv.symm

theorem extend_hillL2TraceGradientCurve_endpoints (q : Coeff 2) (z : ℂ) :
    extend (hillL2TraceGradientCurve q z) 1=extend (hillL2TraceGradientCurve q z) 0 := by
  have hf := integral_deriv_eq_sub_complex (absolutelyContinuousOnInterval_hillL2TraceGradientCurve q z)
    (intervalIntegrable_deriv_hillL2TraceGradientCurve q z)
  have he : (∫ x in (0:ℝ)..1,deriv (extend (hillL2TraceGradientCurve q z)) x)=
      ∫ x in (0:ℝ)..1,extend (hillL2TraceGradientSpatialCurve q z) x := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
    filter_upwards [ae_hasDerivAt_hillL2TraceGradientCurve q z] with x hx
    exact hx.deriv
  rw [he,integral_hillL2TraceGradientSpatialCurve_eq_zero] at hf
  exact sub_eq_zero.mp hf.symm

/-- Weak spatial derivative identity against an arbitrary periodic AC test. -/
theorem integral_hillL2TraceGradientSpatialCurve_mul_test
    (q : Coeff 2) (z : ℂ) (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hfi : IntervalIntegrable (deriv f) volume 0 1) (hend : f 1=f 0) :
    (∫ x in (0:ℝ)..1, f x*extend (hillL2TraceGradientSpatialCurve q z) x)=
      -(∫ x in (0:ℝ)..1, deriv f x*extend (hillL2TraceGradientCurve q z) x) := by
  have hi := integral_mul_deriv_eq_complex hf
    (absolutelyContinuousOnInterval_hillL2TraceGradientCurve q z) hfi
    (intervalIntegrable_deriv_hillL2TraceGradientCurve q z)
  rw [hend,extend_hillL2TraceGradientCurve_endpoints,sub_self,zero_sub] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillL2TraceGradientCurve q z] with x hx
  rw [hx.deriv]

/-- Actual Fourier realization of every endpoint-matching physical curve. -/
theorem hillPhysicalDirection_unitCurveCoefficients (f : Curve ℂ)
    (he : extend f 0=extend f 1) :
    (fun x => -(hillPhysicalDirection (Coeff.periodDouble (unitCurveCoefficientsCLM f))).ofLp.2 x)
      =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] extend f := by
  let X := Coeff.periodDouble (unitCurveCoefficientsCLM f)
  have hr := physicalRestrictionL2_representative (hillFirstOrderDirection X)
  have hn := circle_ae_pullback (Lp.coeFn_neg (l2Synthesis X))
  have hn1 := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1:ℝ)≤2)) hn
  have hX : circlePullback (l2Synthesis X)=ᵐ[volume.restrict (Ioc (0:ℝ) 1)] extend f := by
    dsimp only [X]
    rw [unitCurveCoefficientsCLM_apply,unitCurveCoefficients_eq_continuousPeriodOneCoefficients f he]
    exact circlePullback_continuousPeriodOneCoefficients _ _ _
  filter_upwards [hr,hn1,hX] with x hx hneg hf
  have hs := congrArg Prod.snd hx
  change (hillPhysicalDirection X).ofLp.2 x=circlePullback (l2Synthesis (-X)) x at hs
  change circlePullback (-l2Synthesis X) x= -circlePullback (l2Synthesis X) x at hneg
  change -(hillPhysicalDirection X).ofLp.2 x=_
  rw [hs,map_neg,hneg,neg_neg]
  exact hf

/-- The actual trace derivative on physical continuous curve directions. -/
theorem fderiv_hillL2Discriminant_unitCurveCoefficients
    (q : Coeff 2) (E : ℂ) (f : Curve ℂ) (he : extend f 0=extend f 1) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q)
      (Coeff.periodDouble (unitCurveCoefficientsCLM f))=
        unitComplexCurveIntegral (f*hillL2TraceGradientCurve q (Complex.sqrt E)) := by
  rw [fderiv_hillL2Discriminant_eq_traceGradient_integral,unitComplexCurveIntegral_apply]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_unitCurveCoefficients f he] with x hx
  rw [hx]
  rfl

end NLS.KdV
