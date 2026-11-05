import NLS.KdV.HillDirichletGradientCurves

/-! # The actual rough Hill second derivative

The physical coefficient is an L² representative; no derivative of it
is introduced. The scalar state satisfies y''=(q-mu)y almost everywhere.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillIntervalPotential (q : Coeff 2) (x : ℝ) : ℂ :=
  -(intervalL2Representative (physicalRestrictionL2 (hillFirstOrderPotential q)) x).2

theorem ae_hasDerivAt_hillL2FrequencyStateCurve_snd (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun r : ℝ => (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z v) r).2)
        ((hillIntervalPotential q x-z^2)*(NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z v) x).1) x := by
  filter_upwards [ae_hasDerivAt_l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z
      (constantUpperInitialVector z v),hillFirstOrder_upper_eq_neg_one_ae q] with x hx hu
  have hd := ((constantUpperStateMap z).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x hx
  have hs := HasFDerivAt.hasDerivAt hd.snd
  convert! hs using 1
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
  let a := NLS.LinearVolterra.extend
    (l2SolutionCurve (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v)) x
  let phi := intervalL2Representative (physicalRestrictionL2 (hillFirstOrderPotential q)) x
  change (-phi.2-z^2)*a.1 = (constantUpperStateMap z (classicalODECoefficient phi z a)).2
  have hp : phi.1 = -1 := hu
  simp only [constantUpperStateMap_apply,classicalODECoefficient_apply,hp]
  ring_nf
  simp only [I_sq]
  ring

theorem memLp_hillIntervalPotential (q : Coeff 2) :
    MemLp (hillIntervalPotential q) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (memLp_intervalL2Representative (physicalRestrictionL2 (hillFirstOrderPotential q))).snd.neg

end NLS.KdV
