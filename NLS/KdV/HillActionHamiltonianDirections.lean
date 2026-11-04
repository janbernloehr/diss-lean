import NLS.KdV.HillPhysicalGradientPairing

/-! # Actual action Hamiltonian directions in physical weak form

The bounded test pairing uses the actual source-to-physical L2 map.
The normalized contour tangent satisfies the Gardner integration-by-parts
identity against every periodic AC test with continuous periodic derivative.
No action gradient or Fourier realization is supplied as a hypothesis.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ComplexAnalysis NLS.Fourier
namespace NLS.KdV

/-- The genuine unconjugated unit-interval physical pairing with a fixed
continuous test, as a bounded complex-linear functional on L2 sources. -/
def hillPhysicalCurvePairing (f : Curve ℂ) : Coeff 2 →L[ℂ] ℂ :=
  -((ContinuousMap.evalCLM ℂ (⟨1,by norm_num⟩ : Icc (0:ℝ) 1)).comp
    ((ContinuousLinearMap.apply ℂ (Curve ℂ) f).comp
      (l2ScalarVolterraCLM.comp ((WithLp.sndL 2 ℂ IntervalL2 IntervalL2).comp hillPhysicalDirection))))

theorem hillPhysicalCurvePairing_apply (f : Curve ℂ) (h : Coeff 2) :
    hillPhysicalCurvePairing f h=
      ∫ x in (0:ℝ)..1, extend f x*(-(hillPhysicalDirection h).ofLp.2 x) := by
  change -(∫ x in (0:ℝ)..1, (hillPhysicalDirection h).ofLp.2 x*extend f x)=_
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x _
  ring

theorem hillPhysicalCurvePairing_gardnerDirection (f : Curve ℂ) (q : Coeff 2) (E : ℂ) :
    hillPhysicalCurvePairing f (hillL2DiscriminantGardnerDirection q E)=
      ∫ x in (0:ℝ)..1, extend f x*extend (hillL2TraceGradientSpatialCurve q (Complex.sqrt E)) x := by
  rw [hillPhysicalCurvePairing_apply]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_discriminantGardnerDirection q E] with x hx
  rw [hx]

/-- The actual trace Hamiltonian weak pairing with any periodic AC test
and its actual continuous periodic derivative. -/
theorem hillPhysicalCurvePairing_gardnerDirection_eq_neg_trace_derivative
    (f g : Curve ℂ) (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hfg : deriv (extend f)=ᵐ[volume.restrict (Ioc (0:ℝ) 1)] extend g)
    (hfend : extend f 0=extend f 1) (hgend : extend g 0=extend g 1)
    (q : Coeff 2) (E : ℂ) :
    hillPhysicalCurvePairing f (hillL2DiscriminantGardnerDirection q E)=
      -(fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) q)
        (Coeff.periodDouble (unitCurveCoefficientsCLM g)) := by
  have hfi : IntervalIntegrable (deriv (extend f)) volume 0 1 := by
    apply ((continuous_extend g).intervalIntegrable 0 1).congr_ae
    simpa only [uIoc_of_le (by norm_num : (0:ℝ)≤1)] using hfg.symm
  rw [hillPhysicalCurvePairing_gardnerDirection,
    integral_hillL2TraceGradientSpatialCurve_mul_test q (Complex.sqrt E) (extend f) hf hfi hfend.symm,
    fderiv_hillL2Discriminant_unitCurveCoefficients q E g hgend,unitComplexCurveIntegral_apply]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
  filter_upwards [hfg] with x hx
  rw [hx]
  rfl

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual normalized contour tangent is the physical Gardner
Hamiltonian direction of the action, in weak physical form. This applies
to every matching differentiable action extension, including closed gaps. -/
theorem hillL2TracePeriodDirection_action_hamiltonian_identity
    (m : ℕ) (hm : 1≤m) (A : Coeff 2 → ℂ)
    (hA : DifferentiableAt ℂ A (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      A (SpectralWeight.one.toCoeff p.val)=(hillRealGapIntegral p.val p.property.1 p.property.2 m 0:ℂ))
    (f g : Curve ℂ) (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hfg : deriv (extend f)=ᵐ[volume.restrict (Ioc (0:ℝ) 1)] extend g)
    (hfend : extend f 0=extend f 1) (hgend : extend g 0=extend g 1) :
    hillPhysicalCurvePairing f (hillL2TracePeriodDirection q hq hr m)=
      -(fderiv ℂ A (SpectralWeight.one.toCoeff q)) (Coeff.periodDouble (unitCurveCoefficientsCLM g)) := by
  rw [apply_hillL2TracePeriodDirection q hq hr m hm,
    fderiv_hillRealGapAction_extension_apply q hq hr m hm A hA hmatch _ (Coeff.periodDouble_mem _)]
  have he : (fun E => hillPhysicalCurvePairing f
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) E)/hillEnergyCanonicalRootProduct q hq hr E)=
      (fun E => (-1:ℂ)*((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (SpectralWeight.one.toCoeff q))
        (Coeff.periodDouble (unitCurveCoefficientsCLM g))/hillEnergyCanonicalRootProduct q hq hr E)) := by
    funext E
    rw [hillPhysicalCurvePairing_gardnerDirection_eq_neg_trace_derivative f g hf hfg hfend hgend]
    ring
  rw [he,circleIntegral.integral_const_mul]
  ring

end NLS.KdV
