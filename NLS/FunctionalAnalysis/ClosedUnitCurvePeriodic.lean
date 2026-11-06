import NLS.FunctionalAnalysis.LinearVolterra
import Mathlib.Topology.Instances.AddCircle.Real

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.FunctionalAnalysis



private theorem extend_endpoints (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) :
    NLS.LinearVolterra.extend f 0=NLS.LinearVolterra.extend f 1 := by
  dsimp only [NLS.LinearVolterra.extend]
  rw [projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num),
    projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num)]
  exact hf

def closedUnitCurveCircle (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) : C(AddCircle (1 : ℝ),ℂ) :=
  ⟨AddCircle.liftIoc (1 : ℝ) 0 (NLS.LinearVolterra.extend f),
    AddCircle.liftIoc_zero_continuous (extend_endpoints f hf) (continuous_extend f).continuousOn⟩

def closedUnitCurvePeriodic (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) (x : ℝ) : ℂ :=
  closedUnitCurveCircle f hf (x : AddCircle (1 : ℝ))

theorem continuous_closedUnitCurvePeriodic (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) :
    Continuous (closedUnitCurvePeriodic f hf) :=
  (closedUnitCurveCircle f hf).continuous.comp (by fun_prop)

theorem periodic_closedUnitCurvePeriodic (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) :
    Function.Periodic (closedUnitCurvePeriodic f hf) 1 := by
  intro x
  simp only [closedUnitCurvePeriodic,AddCircle.coe_add,AddCircle.coe_period,add_zero]

theorem closedUnitCurvePeriodic_eq (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) (x : ℝ) (hx : x∈Ioc (0 : ℝ) 1) :
    closedUnitCurvePeriodic f hf x=NLS.LinearVolterra.extend f x := by
  exact AddCircle.liftIoc_zero_coe_apply (f := NLS.LinearVolterra.extend f) hx

def closedUnitCurvePeriodTwo (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) : C(AddCircle (2 : ℝ),ℂ) :=
  let hper : Function.Periodic (closedUnitCurvePeriodic f hf) (2 : ℝ) := by
    simpa only [nsmul_eq_mul,Nat.cast_ofNat,mul_one] using (periodic_closedUnitCurvePeriodic f hf).nsmul 2
  ⟨hper.lift,by
    apply continuous_quot_lift
    exact continuous_closedUnitCurvePeriodic f hf⟩

theorem closedUnitCurvePeriodTwo_coe (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) (x : ℝ) :
    closedUnitCurvePeriodTwo f hf (x : AddCircle (2 : ℝ))=closedUnitCurvePeriodic f hf x := rfl

theorem periodic_closedUnitCurvePeriodTwo (f : Curve ℂ)
    (hf : f ⟨0,by norm_num⟩=f ⟨1,by norm_num⟩) :
    Function.Periodic (fun x : ℝ => closedUnitCurvePeriodTwo f hf (x : AddCircle (2 : ℝ))) 1 :=
  periodic_closedUnitCurvePeriodic f hf

end NLS.FunctionalAnalysis
