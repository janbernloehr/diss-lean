import NLS.KdV.HillL2DirichletCharacteristic
import NLS.ComplexAnalysis.ScalarStateMass

/-! # The actual rough scalar Hill state curve and its physical normalization. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory Matrix
open scoped ComplexConjugate ENNReal
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

def hillL2FrequencyStateCurve (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  (⟨constantUpperStateMap z,(constantUpperStateMap z).continuous⟩ : C(ℂ × ℂ,ℂ × ℂ)).comp
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v))

@[simp] theorem hillL2FrequencyStateCurve_apply (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    hillL2FrequencyStateCurve q z v t = constantUpperStateMap z
      (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v) t) := rfl

@[simp] theorem hillL2FrequencyStateCurve_zero (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) :
    hillL2FrequencyStateCurve q z v ⟨0,by norm_num⟩=v := by
  simp only [hillL2FrequencyStateCurve_apply,l2SolutionCurve_zero,constantUpperStateMap_initialVector]

theorem continuous_hillL2FrequencyStateCurve (z : ℂ) (v : ℂ × ℂ) :
    Continuous (fun q : Coeff 2 => hillL2FrequencyStateCurve q z v) := by
  have hphi : Continuous (fun q : Coeff 2 => hillFirstOrderPotential q) :=
    continuous_const.prodMk continuous_id.neg
  have hu : Continuous (fun q : Coeff 2 => physicalRestrictionL2 (hillFirstOrderPotential q)) :=
    physicalRestrictionL2CLM.continuous.comp hphi
  have hp : Continuous (fun q : Coeff 2 => (z,physicalRestrictionL2 (hillFirstOrderPotential q))) :=
    continuous_const.prodMk hu
  have hs : Continuous (fun q : Coeff 2 => l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z
      (constantUpperInitialVector z v)) := by
    simpa only [Function.comp_def] using
      (continuous_l2SolutionCurve_joint (constantUpperInitialVector z v)).comp hp
  simpa only [hillL2FrequencyStateCurve,Function.comp_def] using
    (ContinuousMap.continuous_postcomp
      (⟨constantUpperStateMap z,(constantUpperStateMap z).continuous⟩ : C(ℂ × ℂ,ℂ × ℂ))).comp hs

theorem hillL2FrequencyStateCurve_eq_classical (Q : C(AddCircle (2 : ℝ),ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    hillL2FrequencyStateCurve (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z v t =
      classicalHillFlow (hillUnitPotentialCurve Q) (z^2) v t := by
  rw [hillL2FrequencyStateCurve_apply,physicalRestrictionL2_of_continuous _ _
    (hillFirstOrder_continuous_compatibility Q),l2SolutionCurve_of_continuous,classicalSolutionCurve_apply]
  exact (classicalHillFlow_eq_constantUpper (hillUnitPotentialCurve Q) z v t).symm


end NLS.KdV
