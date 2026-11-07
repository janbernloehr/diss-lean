import NLS.KdV.ClassicalSourcePrimitive
import NLS.KdV.HillClassicalIdentification
import NLS.ComplexAnalysis.TracePrimitiveFunctoriality

/-! # The classical Hill sheets as a trace family

The shared trace-family construction is definitionally the existing
classical continuation. Restricting a continuous circle potential to the
unit interval is a bounded complex linear realization.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillTraceFamily : TracePrimitiveFamily (Curve ℂ) where
  trace := fun t => classicalHillDiscriminant t.2 t.1
  analytic_trace := analyticOnNhd_classicalHillDiscriminant_joint
  freePrimitive := classicalHillFreePrimitive
  freeDomain := slitPlane
  isOpen_freeDomain := isOpen_slitPlane
  analytic_freePrimitive := analyticOnNhd_classicalHillFreePrimitive
  free_trace := two_cosh_classicalHillFreePrimitive

theorem classicalHillTraceFamily_continuationDomain :
    classicalHillTraceFamily.continuationDomain = classicalHillContinuationDomain := rfl

theorem classicalHillTraceFamily_root :
    classicalHillTraceFamily.root = classicalHillContinuedRoot := rfl

theorem classicalHillTraceFamily_primitive :
    classicalHillTraceFamily.primitive = classicalHillContinuedPrimitive := rfl

def hillUnitPotentialCurveCLM : C(AddCircle (2 : ℝ), ℂ) →L[ℂ] Curve ℂ :=
  ContinuousMap.compCLM ℂ ℂ
    (⟨fun t : Icc (0 : ℝ) 1 => ((t : ℝ) : AddCircle (2 : ℝ)),by fun_prop⟩)

theorem hillUnitPotentialCurveCLM_apply (Q : C(AddCircle (2 : ℝ), ℂ)) :
    hillUnitPotentialCurveCLM Q = hillUnitPotentialCurve Q := rfl

end NLS.KdV
