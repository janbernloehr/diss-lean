import NLS.KdV.ClassicalSourcePrimitive
import NLS.KdV.HillL2HighContourMoments
import NLS.KdV.ActionHamiltonianMoments
import NLS.ComplexAnalysis.TracePrimitiveFunctoriality

/-! # Exact agreement of the continuous and L2 Hill primitives

The actual Fourier realization is bounded complex linear and preserves
the whole normalized trace. Source functoriality identifies both open
continuation domains, roots and primitives without a sign or logarithm
period ambiguity. The L2 Arnold period is consequently the literal
continuous primitive action on each checked high energy circle.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillTraceFamily : TracePrimitiveFamily (Curve ℂ) where
  trace := fun t => classicalHillDiscriminant t.2 t.1
  analytic_trace := analyticOnNhd_classicalHillDiscriminant_joint
  freePrimitive := classicalHillFreePrimitive
  freeDomain := slitPlane
  isOpen_freeDomain := isOpen_slitPlane
  analytic_freePrimitive := analyticOnNhd_classicalHillFreePrimitive
  free_trace := two_cosh_classicalHillFreePrimitive

@[simp] theorem classicalHillTraceFamily_domain :
    classicalHillTraceFamily.continuationDomain = classicalHillContinuationDomain := rfl

@[simp] theorem classicalHillTraceFamily_root :
    classicalHillTraceFamily.root = classicalHillContinuedRoot := rfl

@[simp] theorem classicalHillTraceFamily_primitive :
    classicalHillTraceFamily.primitive = classicalHillContinuedPrimitive := rfl

def hillUnitPotentialCLM : C(AddCircle (2 : ℝ), ℂ) →L[ℂ] Curve ℂ :=
  ContinuousMap.compCLM ℂ (R := ℂ)
    ⟨fun t : Icc (0 : ℝ) 1 => ((t : ℝ) : AddCircle (2 : ℝ)),by fun_prop⟩

@[simp] theorem hillUnitPotentialCLM_apply (Q : C(AddCircle (2 : ℝ), ℂ)) :
    hillUnitPotentialCLM Q = hillUnitPotentialCurve Q := rfl

theorem toCoeff_hillContinuousCoefficients (Q : C(AddCircle (2 : ℝ), ℂ)) :
    SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) = Fourier.continuousFourierCLM Q := by
  ext k
  simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,
    Fourier.continuousFourierCLM_apply]

private def circleFamily := classicalHillTraceFamily.pullback hillUnitPotentialCLM

private theorem trace_agreement (z : ℂ) (Q : C(AddCircle (2 : ℝ), ℂ)) :
    hillL2SourceFamily.trace (z,Fourier.continuousFourierCLM Q) = circleFamily.trace (z,Q) := by
  change hillL2Discriminant (Fourier.continuousFourierCLM Q) z =
    classicalHillDiscriminant (hillUnitPotentialCurve Q) z
  rw [← toCoeff_hillContinuousCoefficients]
  exact hillL2Discriminant_eq_classical Q z

theorem hillL2ContinuationDomain_iff_classical (Q : C(AddCircle (2 : ℝ), ℂ)) (z : ℂ) :
    (z,SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) ∈ hillL2ContinuationDomain ↔
      (z,hillUnitPotentialCurve Q) ∈ classicalHillContinuationDomain := by
  rw [toCoeff_hillContinuousCoefficients]
  have hL := TracePrimitiveFamily.continuationDomain_comp_iff circleFamily hillL2SourceFamily
    Fourier.continuousFourierCLM trace_agreement rfl z Q
  have hC := TracePrimitiveFamily.continuationDomain_comp_iff circleFamily classicalHillTraceFamily
    hillUnitPotentialCLM (fun _ _ => rfl) rfl z Q
  exact hL.trans hC.symm

theorem hillL2ContinuedRoot_eq_classical (Q : C(AddCircle (2 : ℝ), ℂ)) (z : ℂ)
    (hz : (z,hillUnitPotentialCurve Q) ∈ classicalHillContinuationDomain) :
    hillL2ContinuedRoot (z,SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) =
      classicalHillContinuedRoot (z,hillUnitPotentialCurve Q) := by
  have hc := TracePrimitiveFamily.continuationDomain_comp_iff circleFamily classicalHillTraceFamily
    hillUnitPotentialCLM (fun _ _ => rfl) rfl z Q
  have ht : (z,Q) ∈ circleFamily.continuationDomain := hc.mp hz
  have hL := TracePrimitiveFamily.root_comp circleFamily hillL2SourceFamily Fourier.continuousFourierCLM
    trace_agreement (fun _ => rfl) rfl z Q ht
  have hC := TracePrimitiveFamily.root_comp circleFamily classicalHillTraceFamily hillUnitPotentialCLM
    (fun _ _ => rfl) (fun _ => rfl) rfl z Q ht
  rw [toCoeff_hillContinuousCoefficients]
  exact hL.trans hC.symm

theorem hillL2ContinuedPrimitive_eq_classical (Q : C(AddCircle (2 : ℝ), ℂ)) (z : ℂ)
    (hz : (z,hillUnitPotentialCurve Q) ∈ classicalHillContinuationDomain) :
    hillL2ContinuedPrimitive (z,SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) =
      classicalHillContinuedPrimitive (z,hillUnitPotentialCurve Q) := by
  have hc := TracePrimitiveFamily.continuationDomain_comp_iff circleFamily classicalHillTraceFamily
    hillUnitPotentialCLM (fun _ _ => rfl) rfl z Q
  have ht : (z,Q) ∈ circleFamily.continuationDomain := hc.mp hz
  have hL := TracePrimitiveFamily.primitive_comp circleFamily hillL2SourceFamily Fourier.continuousFourierCLM
    trace_agreement (fun _ => rfl) rfl z Q ht
  have hC := TracePrimitiveFamily.primitive_comp circleFamily classicalHillTraceFamily hillUnitPotentialCLM
    (fun _ _ => rfl) (fun _ => rfl) rfl z Q ht
  rw [toCoeff_hillContinuousCoefficients]
  exact hL.trans hC.symm

theorem hillL2HighContourMoment_zero_eq_classicalPrimitiveAction
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hQ : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖hillContinuousCoefficients Q‖ ≤ (n : ℝ)) :
    hillL2HighContourMoment n 0 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) =
      primitiveAction (fun z => classicalHillContinuedPrimitive (z,hillUnitPotentialCurve Q))
        (freeHillValue n : ℂ) (n : ℝ) := by
  unfold hillL2HighContourMoment TracePrimitiveFamily.contourMoment primitiveAction
  simp only [pow_zero,one_mul]
  congr 1
  apply circleIntegral.integral_congr (by positivity)
  intro z hz
  have hd := mem_hillL2ContinuationDomain_high_sphere (hillContinuousCoefficients Q)
    (hillContinuousCoefficients_mem_even Q hQ) n hn hcut z hz
  exact hillL2ContinuedPrimitive_eq_classical Q z ((hillL2ContinuationDomain_iff_classical Q z).mp hd)

/-- The L2 Arnold period agrees with the article's indexed primitive
normalization F_n=F+i*n*pi, with its factor -1/pi unchanged. -/
theorem hillL2HighContourMoment_zero_eq_shifted_classicalPrimitiveAction
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hQ : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 8*‖hillContinuousCoefficients Q‖ ≤ (n : ℝ)) :
    hillL2HighContourMoment n 0 (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) =
      primitiveAction (fun z => classicalHillContinuedPrimitive (z,hillUnitPotentialCurve Q)+I*(n : ℂ)*Real.pi)
        (freeHillValue n : ℂ) (n : ℝ) := by
  rw [hillL2HighContourMoment_zero_eq_classicalPrimitiveAction Q hQ n hn hcut]
  let D : Set ℂ := {z | (z,hillUnitPotentialCurve Q) ∈ classicalHillContinuationDomain}
  have hF : AnalyticOnNhd ℂ (fun z => classicalHillContinuedPrimitive (z,hillUnitPotentialCurve Q)) D := by
    intro z hz
    exact (analyticOnNhd_classicalHillContinuedPrimitive _ hz).comp
      (f := fun z : ℂ => (z,hillUnitPotentialCurve Q)) (analyticAt_id.prod analyticAt_const)
  have hcircle : sphere (freeHillValue n : ℂ) (n : ℝ) ⊆ D := by
    intro z hz
    exact (hillL2ContinuationDomain_iff_classical Q z).mp
      (mem_hillL2ContinuationDomain_high_sphere (hillContinuousCoefficients Q)
        (hillContinuousCoefficients_mem_even Q hQ) n hn hcut z hz)
  have hi : CircleIntegrable (fun z => classicalHillContinuedPrimitive (z,hillUnitPotentialCurve Q))
      (freeHillValue n : ℂ) (n : ℝ) := (hF.continuousOn.mono hcircle).circleIntegrable (by positivity)
  have hc : (∮ z in C((freeHillValue n : ℂ),(n : ℝ)), I*(n : ℂ)*Real.pi) = 0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt (by positivity)
      (f := fun z : ℂ => (I*(n : ℂ)*Real.pi)*z)
      (fun z _ => by simpa only [mul_one,id_eq] using! ((hasDerivAt_id z).const_mul (I*(n : ℂ)*Real.pi)).hasDerivWithinAt)
  unfold primitiveAction
  rw [circleIntegral.integral_add hi (circleIntegrable_const _ _ _),hc,add_zero]

end NLS.KdV
