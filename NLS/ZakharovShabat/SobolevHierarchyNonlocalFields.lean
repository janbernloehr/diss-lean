import NLS.ZakharovShabat.SobolevHierarchyPhysicalFields
import NLS.FunctionalAnalysis.UnitComplexCurvePrimitive

/-! # Bounded continuous fields in the sharp nonlocal Hamiltonian recurrence -/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

def hierarchyCircleUnitRestriction : C(AddCircle (2:ℝ),ℂ) →L[ℂ] Curve ℂ :=
  ContinuousMap.compCLM ℂ (R := ℂ)
    ⟨fun t : Icc (0:ℝ) 1 => ((t : ℝ) : AddCircle (2:ℝ)),by fun_prop⟩

def hierarchyUnitPotential (s : ℕ) (ab : SobolevSource s) : Curve ℂ × Curve ℂ :=
  (hierarchyCircleUnitRestriction (lowerSobolevJet s (false,0) ab),
   hierarchyCircleUnitRestriction (lowerSobolevJet s (true,0) ab))

def hierarchyUnitGradient (s k : ℕ) (ab : SobolevSource s) : Curve ℂ × Curve ℂ :=
  (hierarchyCircleUnitRestriction (sobolevNLSHierarchyContinuousGradient s k ab).1,
   hierarchyCircleUnitRestriction (sobolevNLSHierarchyContinuousGradient s k ab).2)

def hierarchyRPairingCurve (s k : ℕ) (ab : SobolevSource s) : Curve ℂ :=
  I • ((hierarchyUnitPotential s ab).1*(hierarchyUnitGradient s k ab).1)-
    I • ((hierarchyUnitPotential s ab).2*(hierarchyUnitGradient s k ab).2)

def hierarchyNonlocalPrimitive (s k : ℕ) (ab : SobolevSource s) : Curve ℂ :=
  unitComplexCurvePrimitive (hierarchyRPairingCurve s k ab)

def hierarchyIntegratedNonlocal (s k : ℕ) (ab : SobolevSource s) : Curve ℂ × Curve ℂ :=
  (unitComplexCurvePrimitive ((hierarchyUnitPotential s ab).2*hierarchyNonlocalPrimitive s k ab),
   unitComplexCurvePrimitive (-((hierarchyUnitPotential s ab).1*hierarchyNonlocalPrimitive s k ab)))

theorem continuous_hierarchyUnitPotential (s : ℕ) : Continuous (hierarchyUnitPotential s) :=
  (hierarchyCircleUnitRestriction.continuous.comp (lowerSobolevJet s (false,0)).continuous).prodMk
    (hierarchyCircleUnitRestriction.continuous.comp (lowerSobolevJet s (true,0)).continuous)

theorem continuous_hierarchyUnitGradient (s k : ℕ) : Continuous (hierarchyUnitGradient s k) := by
  have hc : Continuous (sobolevNLSHierarchyContinuousGradient s k) :=
    continuous_iff_continuousAt.mpr fun ab => (analyticAt_sobolevNLSHierarchyContinuousGradient s k ab).continuousAt
  exact (hierarchyCircleUnitRestriction.continuous.comp hc.fst).prodMk
    (hierarchyCircleUnitRestriction.continuous.comp hc.snd)

theorem continuous_hierarchyRPairingCurve (s k : ℕ) : Continuous (hierarchyRPairingCurve s k) :=
  ((continuous_hierarchyUnitPotential s).fst.mul (continuous_hierarchyUnitGradient s k).fst).const_smul I |>.sub
    (((continuous_hierarchyUnitPotential s).snd.mul (continuous_hierarchyUnitGradient s k).snd).const_smul I)

theorem continuous_hierarchyNonlocalPrimitive (s k : ℕ) : Continuous (hierarchyNonlocalPrimitive s k) :=
  unitComplexCurvePrimitive.continuous.comp (continuous_hierarchyRPairingCurve s k)

theorem continuous_hierarchyIntegratedNonlocal (s k : ℕ) : Continuous (hierarchyIntegratedNonlocal s k) :=
  (unitComplexCurvePrimitive.continuous.comp
    ((continuous_hierarchyUnitPotential s).snd.mul (continuous_hierarchyNonlocalPrimitive s k))).prodMk
      (unitComplexCurvePrimitive.continuous.comp
        (((continuous_hierarchyUnitPotential s).fst.mul (continuous_hierarchyNonlocalPrimitive s k)).neg))

theorem hierarchyUnitPotential_eq_classical
    (s : ℕ) (hs : 1 ≤ s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) (t : Icc (0:ℝ) 1) :
    ((hierarchyUnitPotential s ab).1 t,(hierarchyUnitPotential s ab).2 t) = (a t,b t) := by
  have h₁ := lowerSobolevJet_eq_classical s ab a b ha hb hpa hpb haq hbq (false,0) (by omega) t
  have h₂ := lowerSobolevJet_eq_classical s ab a b ha hb hpa hpb haq hbq (true,0) (by omega) t
  exact Prod.ext h₁ h₂

theorem hierarchyUnitGradient_eq_classical
    (s k : ℕ) (hs : 1 ≤ s) (hk : k ≤ s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j) (t : Icc (0:ℝ) 1) :
    ((hierarchyUnitGradient s k ab).1 t,(hierarchyUnitGradient s k ab).2 t) =
      classicalNLSHierarchyGradient a b k t :=
  sobolevNLSHierarchyContinuousGradient_eq_classical s k hs hk ab a b ha hb hpa hpb haq hbq t

end NLS.ZakharovShabat
