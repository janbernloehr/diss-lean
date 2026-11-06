import NLS.KdV.HillRoughScalarEquation
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

/-- Compatibility name for the same original physical L² representative. -/
abbrev hillIntervalPotential (q : Coeff 2) (x : ℝ) : ℂ :=
  hillL2ScalarRepresentative q x

theorem memLp_hillIntervalPotential (q : Coeff 2) :
    MemLp (hillIntervalPotential q) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (memLp_intervalL2Representative (physicalRestrictionL2 (hillFirstOrderPotential q))).snd.neg

end NLS.KdV
