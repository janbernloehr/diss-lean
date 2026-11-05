import NLS.KdV.HillDirichletGradients

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

def hillL2DirichletSlopeDirectionKernel (q h : Coeff 2) (z : ℂ) : ℂ :=
  (constantUpperStateMap z (l2PotentialKernelCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) (hillPhysicalDirection h)
    z (0,I) ⟨1,by norm_num⟩)).2

theorem fderiv_hillL2FrequencyDirichletSlope_potential (q h : Coeff 2) (z : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2FrequencyDirichletSlope p z) q) h=
      hillL2DirichletSlopeDirectionKernel q h z := by
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  let U (p : Coeff 2) := physicalRestrictionL2 (hillFirstOrderPotential p)
  let S (w : IntervalPairL2) := l2SolutionCurve w z (0,I)
  have hS : DifferentiableAt ℂ S u := by
    exact ((analyticOnNhd_l2SolutionCurve_joint (0,I) (z,u) (mem_univ _)).comp
      (f := fun w : IntervalPairL2 => (z,w)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hcomp := hS.hasFDerivAt.comp q (hasFDerivAt_hillPhysicalPotential q)
  let E : Curve (ℂ × ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).comp
      ((constantUpperStateMap z).comp (ContinuousMap.evalCLM ℂ ⟨1,by norm_num⟩))
  have heval := E.hasFDerivAt.comp q hcomp
  have heq : (fun p : Coeff 2 => E (S (U p)))=(fun p : Coeff 2 => hillL2FrequencyDirichletSlope p z) := by
    funext p
    simp only [E,S,U,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',
      ContinuousMap.evalCLM_apply,hillL2FrequencyDirichletSlope,constantUpperStateMap_apply,
      constantUpperInitialVector,mul_zero,mul_one,sub_zero]
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) heval.fderiv
  change (fderiv ℂ (fun p : Coeff 2 => E (S (U p))) q) h=
    E ((fderiv ℂ S u) (hillPhysicalDirection h)) at he
  rw [heq] at he
  rw [he]
  dsimp only [S]
  rw [fderiv_l2SolutionCurve_potential_eq_kernel]
  rfl

theorem fderiv_hillL2DirichletSlope_potential (q h : Coeff 2) (energy : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p energy) q) h=
      hillL2DirichletSlopeDirectionKernel q h (Complex.sqrt energy) :=
  fderiv_hillL2FrequencyDirichletSlope_potential q h (Complex.sqrt energy)

end NLS.KdV
