import NLS.KdV.HillDirichletSlope
import NLS.ZakharovShabat.L2VariationKernel

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

def hillFirstOrderDirection : Coeff 2 →L[ℂ] PairSpace 2 :=
  (0 : Coeff 2 →L[ℂ] Coeff 2).prod (-(ContinuousLinearMap.id ℂ (Coeff 2)))

@[simp] theorem hillFirstOrderDirection_apply (h : Coeff 2) :
    hillFirstOrderDirection h=(0,-h) := rfl

theorem hasFDerivAt_hillFirstOrderPotential (q : Coeff 2) :
    HasFDerivAt hillFirstOrderPotential hillFirstOrderDirection q := by
  convert! (hasFDerivAt_const (lp.single 2 0 (-1) : Coeff 2) q).prodMk (hasFDerivAt_id q).neg using 1

def hillPhysicalDirection : Coeff 2 →L[ℂ] IntervalPairL2 :=
  physicalRestrictionL2CLM.comp hillFirstOrderDirection

theorem hasFDerivAt_hillPhysicalPotential (q : Coeff 2) :
    HasFDerivAt (fun p : Coeff 2 => physicalRestrictionL2 (hillFirstOrderPotential p)) hillPhysicalDirection q := by
  exact (physicalRestrictionL2CLM.hasFDerivAt).comp q (hasFDerivAt_hillFirstOrderPotential q)

def hillL2DirichletDirectionKernel (q h : Coeff 2) (z : ℂ) : ℂ :=
  (l2PotentialKernelCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) (hillPhysicalDirection h)
    z (0,I) ⟨1,by norm_num⟩).1

theorem fderiv_hillL2FrequencyDirichlet_potential (q h : Coeff 2) (z : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2FrequencyDirichlet p z) q) h=
      hillL2DirichletDirectionKernel q h z := by
  let u := physicalRestrictionL2 (hillFirstOrderPotential q)
  let U (p : Coeff 2) := physicalRestrictionL2 (hillFirstOrderPotential p)
  let S (w : IntervalPairL2) := l2SolutionCurve w z (0,I)
  have hS : DifferentiableAt ℂ S u := by
    exact ((analyticOnNhd_l2SolutionCurve_joint (0,I) (z,u) (mem_univ _)).comp
      (f := fun w : IntervalPairL2 => (z,w)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hcomp := hS.hasFDerivAt.comp q (hasFDerivAt_hillPhysicalPotential q)
  let E : Curve (ℂ × ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousMap.evalCLM ℂ ⟨1,by norm_num⟩)
  have heval := E.hasFDerivAt.comp q hcomp
  have heq : (fun p : Coeff 2 => E (S (U p)))=(fun p : Coeff 2 => hillL2FrequencyDirichlet p z) := by
    funext p
    simp only [E,S,U,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
      ContinuousMap.evalCLM_apply,hillL2FrequencyDirichlet,constantUpperStateMap_apply,
      constantUpperInitialVector,mul_zero,mul_one,sub_zero]
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) heval.fderiv
  change (fderiv ℂ (fun p : Coeff 2 => E (S (U p))) q) h=
    E ((fderiv ℂ S u) (hillPhysicalDirection h)) at he
  rw [heq] at he
  rw [he]
  dsimp only [S]
  rw [fderiv_l2SolutionCurve_potential_eq_kernel]
  rfl

theorem fderiv_hillL2DirichletCharacteristic_potential (q h : Coeff 2) (energy : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2DirichletCharacteristic p energy) q) h=
      hillL2DirichletDirectionKernel q h (Complex.sqrt energy) :=
  fderiv_hillL2FrequencyDirichlet_potential q h (Complex.sqrt energy)

end NLS.KdV
