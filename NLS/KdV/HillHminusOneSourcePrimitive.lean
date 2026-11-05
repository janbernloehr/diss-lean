import NLS.KdV.HillHminusOneDiscriminant
import NLS.KdV.HillL2SourcePrimitive
import NLS.ComplexAnalysis.TracePrimitiveFunctoriality

/-! # Free-normalized source sheets for the actual H^-1 Hill trace

The jointly entire H^-1 trace has its original free value. The shared
source-continuation construction gives a jointly analytic primitive and
root on an explicit open domain. Their restrictions to every unit-period
L2 input agree exactly with the physical L2 sheets, with no new sign or
logarithm period.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

@[simp] theorem hillHminusDiscriminant_zero (lambda : ℂ) :
    hillHminusDiscriminant 0 lambda = 2*cos (sqrt lambda) := by
  have h := hillHminusDiscriminant_eq_hillL2 (0 : Coeff 2) lambda
  simpa only [map_zero,hillL2Discriminant_zero] using h

def hillHminusRadicand (q : PeriodOneHminusOne) (lambda : ℂ) : ℂ :=
  hillHminusDiscriminant q lambda^2-4

theorem analyticOnNhd_hillHminusRadicand_joint :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1) univ :=
  (analyticOnNhd_hillHminusDiscriminant_joint.pow 2).sub analyticOnNhd_const

theorem hillHminusRadicand_eq_hillL2 (q : Coeff 2) (lambda : ℂ) :
    hillHminusRadicand (periodOneL2Inclusion q) lambda = hillL2Radicand (Coeff.periodDouble q) lambda := by
  rw [hillHminusRadicand,hillL2Radicand,hillHminusDiscriminant_eq_hillL2]

def hillHminusSourceFamily : TracePrimitiveFamily PeriodOneHminusOne where
  trace := fun t => hillHminusDiscriminant t.2 t.1
  analytic_trace := analyticOnNhd_hillHminusDiscriminant_joint
  freePrimitive := classicalHillFreePrimitive
  freeDomain := slitPlane
  isOpen_freeDomain := isOpen_slitPlane
  analytic_freePrimitive := analyticOnNhd_classicalHillFreePrimitive
  free_trace := fun z => by
    rw [hillHminusDiscriminant_zero]
    simpa only [classicalHillDiscriminant_zero] using two_cosh_classicalHillFreePrimitive z

def hillHminusContinuationDomain : Set (ℂ × PeriodOneHminusOne) := hillHminusSourceFamily.continuationDomain
def hillHminusContinuedRoot : ℂ × PeriodOneHminusOne → ℂ := hillHminusSourceFamily.root
def hillHminusContinuedPrimitive : ℂ × PeriodOneHminusOne → ℂ := hillHminusSourceFamily.primitive

theorem isOpen_hillHminusContinuationDomain : IsOpen hillHminusContinuationDomain :=
  hillHminusSourceFamily.isOpen_continuationDomain

theorem mem_hillHminusContinuationDomain_iff (t : ℂ × PeriodOneHminusOne) :
    t ∈ hillHminusContinuationDomain ↔ t.1 ∈ slitPlane ∧
      ∀ s ∈ Icc (0 : ℝ) 1, hillHminusRadicand ((s : ℂ) • t.2) t.1 ≠ 0 := by
  constructor
  · intro ht
    refine ⟨(hillHminusSourceFamily.continuationDomain_subset ht).1,?_⟩
    intro s hs
    simpa only [TracePrimitiveFamily.rootDomain,TracePrimitiveFamily.radicand,
      hillHminusSourceFamily,sourceSegmentMap,zero_add,sub_zero,hillHminusRadicand] using (ht s hs).2
  · rintro ⟨hz,hne⟩ s hs
    refine ⟨hz,?_⟩
    simpa only [TracePrimitiveFamily.radicand,hillHminusSourceFamily,sourceSegmentMap,
      zero_add,sub_zero,hillHminusRadicand] using hne s hs

theorem analyticOnNhd_hillHminusContinuedRoot :
    AnalyticOnNhd ℂ hillHminusContinuedRoot hillHminusContinuationDomain :=
  hillHminusSourceFamily.analytic_root

theorem analyticOnNhd_hillHminusContinuedPrimitive :
    AnalyticOnNhd ℂ hillHminusContinuedPrimitive hillHminusContinuationDomain :=
  hillHminusSourceFamily.analytic_primitive

@[simp] theorem hillHminusContinuedPrimitive_base (lambda : ℂ) :
    hillHminusContinuedPrimitive (lambda,0) = -I*sqrt lambda := hillHminusSourceFamily.primitive_base lambda

theorem hillHminusContinuedRoot_sq (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ hillHminusContinuationDomain) :
    hillHminusContinuedRoot t^2 = hillHminusRadicand t.2 t.1 := hillHminusSourceFamily.root_sq t ht

theorem hillHminusContinuedPrimitive_trace (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ hillHminusContinuationDomain) :
    2*cosh (hillHminusContinuedPrimitive t) = hillHminusDiscriminant t.2 t.1 ∧
      2*sinh (hillHminusContinuedPrimitive t) = hillHminusContinuedRoot t :=
  hillHminusSourceFamily.primitive_trace t ht

theorem hasDerivAt_hillHminusContinuedPrimitive (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ hillHminusContinuationDomain) :
    HasDerivAt (fun z => hillHminusContinuedPrimitive (z,t.2))
      (deriv (hillHminusDiscriminant t.2) t.1/hillHminusContinuedRoot t) t.1 :=
  hillHminusSourceFamily.hasDerivAt_primitive t ht

private def unitL2HillSourceFamily : TracePrimitiveFamily (Coeff 2) :=
  hillL2SourceFamily.pullback Coeff.periodDouble.toContinuousLinearMap

private theorem unitL2HillSource_trace (lambda : ℂ) (q : Coeff 2) :
    hillHminusSourceFamily.trace (lambda,periodOneL2Inclusion q) =
      unitL2HillSourceFamily.trace (lambda,q) := hillHminusDiscriminant_eq_hillL2 q lambda

theorem hillHminusContinuationDomain_L2_iff (lambda : ℂ) (q : Coeff 2) :
    (lambda,periodOneL2Inclusion q) ∈ hillHminusContinuationDomain ↔
      (lambda,Coeff.periodDouble q) ∈ hillL2ContinuationDomain := by
  have hH := TracePrimitiveFamily.continuationDomain_comp_iff
    unitL2HillSourceFamily hillHminusSourceFamily periodOneL2Inclusion unitL2HillSource_trace rfl lambda q
  have hL := TracePrimitiveFamily.continuationDomain_comp_iff
    unitL2HillSourceFamily hillL2SourceFamily Coeff.periodDouble.toContinuousLinearMap
    (fun _ _ => rfl) rfl lambda q
  exact hH.trans hL.symm

theorem hillHminusContinuedRoot_eq_hillL2 (lambda : ℂ) (q : Coeff 2)
    (ht : (lambda,Coeff.periodDouble q) ∈ hillL2ContinuationDomain) :
    hillHminusContinuedRoot (lambda,periodOneL2Inclusion q) =
      hillL2ContinuedRoot (lambda,Coeff.periodDouble q) := by
  have hu : (lambda,q) ∈ unitL2HillSourceFamily.continuationDomain :=
    (TracePrimitiveFamily.continuationDomain_comp_iff unitL2HillSourceFamily hillL2SourceFamily
      Coeff.periodDouble.toContinuousLinearMap (fun _ _ => rfl) rfl lambda q).mp ht
  exact (TracePrimitiveFamily.root_comp unitL2HillSourceFamily hillHminusSourceFamily
    periodOneL2Inclusion unitL2HillSource_trace (fun _ => rfl) rfl lambda q hu).trans
      (TracePrimitiveFamily.root_comp unitL2HillSourceFamily hillL2SourceFamily
        Coeff.periodDouble.toContinuousLinearMap (fun _ _ => rfl) (fun _ => rfl) rfl lambda q hu).symm

theorem hillHminusContinuedPrimitive_eq_hillL2 (lambda : ℂ) (q : Coeff 2)
    (ht : (lambda,Coeff.periodDouble q) ∈ hillL2ContinuationDomain) :
    hillHminusContinuedPrimitive (lambda,periodOneL2Inclusion q) =
      hillL2ContinuedPrimitive (lambda,Coeff.periodDouble q) := by
  have hu : (lambda,q) ∈ unitL2HillSourceFamily.continuationDomain :=
    (TracePrimitiveFamily.continuationDomain_comp_iff unitL2HillSourceFamily hillL2SourceFamily
      Coeff.periodDouble.toContinuousLinearMap (fun _ _ => rfl) rfl lambda q).mp ht
  exact (TracePrimitiveFamily.primitive_comp unitL2HillSourceFamily hillHminusSourceFamily
    periodOneL2Inclusion unitL2HillSource_trace (fun _ => rfl) rfl lambda q hu).trans
      (TracePrimitiveFamily.primitive_comp unitL2HillSourceFamily hillL2SourceFamily
        Coeff.periodDouble.toContinuousLinearMap (fun _ _ => rfl) (fun _ => rfl) rfl lambda q hu).symm

end NLS.KdV
