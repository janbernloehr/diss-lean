import NLS.KdV.HillGradientPeriodicTraces
import NLS.FunctionalAnalysis.UnitCurveLpBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Physical periodic H² regularity of the independent Hill cotangents

First gradient derivatives are absolutely continuous and their actual
second derivatives are in L². Periodic values and first-derivative traces
are proved separately, including the log-norming trace equal to one.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem memLp_hillProductSecond (q : ℝ → ℂ) (mu : ℂ) (A C : Curve (ℂ × ℂ))
    (hq : MemLp q 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    MemLp (fun x => 2*(extend A x).2*(extend C x).2+
      2*(q x-mu)*(extend A x).1*(extend C x).1) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  let Af := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp A
  let Ad := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp A
  let Cf := (ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp C
  let Cd := (ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp C
  let R : Curve ℂ := (2 : ℂ) • (Af*Cf)
  let T : Curve ℂ := (2 : ℂ) • (Ad*Cd)-(2*mu) • (Af*Cf)
  have hr : MemLp (fun x => q x*extend R x) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_unitCurve_extend ⊤ R).mul' hq
  have ht := memLp_unitCurve_extend 2 T
  convert! hr.add ht using 1
  funext x
  dsimp only [Pi.add_apply,Pi.sub_apply,R,T,Af,Ad,Cf,Cd,NLS.LinearVolterra.extend,ContinuousMap.smul_apply,
    ContinuousMap.mul_apply,ContinuousMap.sub_apply,ContinuousMap.comp_apply,
    ContinuousMap.fst,ContinuousMap.snd,ContinuousMap.coe_mk,smul_eq_mul]
  ring

theorem memLp_hillDirichletGradientSecond (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    MemLp (hillDirichletGradientSecond q n hn) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have h := memLp_hillProductSecond (hillIntervalPotential (SpectralWeight.one.toCoeff q.val))
    (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)
    (hillDirichletStateCurve q n hn) (hillDirichletStateCurve q n hn)
    (memLp_hillIntervalPotential (SpectralWeight.one.toCoeff q.val))
  convert! h.const_mul ((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹) using 1
  funext x
  unfold hillDirichletGradientSecond
  ring

theorem memLp_hillLogNormingGradientSecond (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    MemLp (hillLogNormingGradientSecond q n hn) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hCS := memLp_hillProductSecond (hillIntervalPotential (SpectralWeight.one.toCoeff q.val))
    (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)
    (hillDirichletCosineCurve q n hn) (hillDirichletStateCurve q n hn)
    (memLp_hillIntervalPotential (SpectralWeight.one.toCoeff q.val))
  have hSS := memLp_hillProductSecond (hillIntervalPotential (SpectralWeight.one.toCoeff q.val))
    (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)
    (hillDirichletStateCurve q n hn) (hillDirichletStateCurve q n hn)
    (memLp_hillIntervalPotential (SpectralWeight.one.toCoeff q.val))
  convert! hCS.sub (hSS.const_mul (hillLogNormingProjection q n hn)) using 1
  funext x
  dsimp only [hillLogNormingGradientSecond,Pi.sub_apply]
  ring

theorem absolutelyContinuousOnInterval_hillDirichletGradientSpatialCurve
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    AbsolutelyContinuousOnInterval (extend (hillDirichletGradientSpatialCurve q n hn)) 0 1 := by
  have h := absolutelyContinuousOnInterval_hillStateCurve (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)
  have hf := absolutelyContinuousOnInterval_clm h (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hd := absolutelyContinuousOnInterval_clm h (ContinuousLinearMap.snd ℝ ℂ ℂ)
  convert! (hf.smul hd).const_smul (2/(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)) using 1

theorem absolutelyContinuousOnInterval_hillLogNormingGradientSpatialCurve
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    AbsolutelyContinuousOnInterval (extend (hillLogNormingGradientSpatialCurve q n hn)) 0 1 := by
  have hS := absolutelyContinuousOnInterval_hillStateCurve (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)
  have hC := absolutelyContinuousOnInterval_hillStateCurve (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (1,0)
  have hSf := absolutelyContinuousOnInterval_clm hS (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hSd := absolutelyContinuousOnInterval_clm hS (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hCf := absolutelyContinuousOnInterval_clm hC (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hCd := absolutelyContinuousOnInterval_clm hC (ContinuousLinearMap.snd ℝ ℂ ℂ)
  convert! ((hCd.smul hSf).add (hCf.smul hSd)).sub
    ((hSf.smul hSd).const_smul (2*hillLogNormingProjection q n hn)) using 1

end NLS.KdV
