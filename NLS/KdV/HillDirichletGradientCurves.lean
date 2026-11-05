import NLS.KdV.HillDirichletSquaredPairing
import NLS.ZakharovShabat.L2WholeLinePeriodAbsoluteContinuity

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ComplexConjugate ENNReal

namespace NLS.KdV

def hillDirichletGradientCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) : Curve ℂ :=
  (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹ •
    (((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillDirichletStateCurve q n hn))^2)

def hillDirichletGradientSpatialCurve (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) : Curve ℂ :=
  (2/(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)) •
    (((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).comp (hillDirichletStateCurve q n hn))*
      ((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).comp (hillDirichletStateCurve q n hn)))

theorem absolutelyContinuousOnInterval_hillStateCurve (q : Coeff 2) (z : ℂ) (v : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillL2FrequencyStateCurve q z v)) 0 1 := by
  have h := absolutelyContinuousOnInterval_l2SolutionCurve
    (physicalRestrictionL2 (hillFirstOrderPotential q)) z (constantUpperInitialVector z v)
  have ht := NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_clm h
    ((constantUpperStateMap z).restrictScalars ℝ)
  convert! ht using 1

theorem absolutelyContinuousOnInterval_hillDirichletGradientCurve
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)) 0 1 := by
  have hs := absolutelyContinuousOnInterval_hillStateCurve (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)
  have hp := NLS.FunctionalAnalysis.absolutelyContinuousOnInterval_clm hs (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hh := (hp.smul hp).const_smul ((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹)
  convert! hh using 1
  funext x
  let A := hillDirichletStateCurve q n hn
  change (scalarStateMass A : ℂ)⁻¹*(NLS.LinearVolterra.extend A x).1^2=
    (scalarStateMass A : ℂ)⁻¹*((NLS.LinearVolterra.extend A x).1*(NLS.LinearVolterra.extend A x).1)
  ring

theorem ae_hasDerivAt_hillDirichletGradientCurve
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn))
        (NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q n hn) x) x := by
  have hs := ae_hasDerivAt_hillL2FrequencyStateCurve_fst (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)
  filter_upwards [hs] with x hx
  have hh := (hx.pow 2).const_mul ((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹)
  convert! hh using 1
  let A := hillDirichletStateCurve q n hn
  change (2/(scalarStateMass A : ℂ))*((NLS.LinearVolterra.extend A x).1*(NLS.LinearVolterra.extend A x).2)=
    (scalarStateMass A : ℂ)⁻¹*((2 : ℂ)*(NLS.LinearVolterra.extend A x).1^(2-1)*(NLS.LinearVolterra.extend A x).2)
  simp only [show 2-1=1 from rfl,pow_one,div_eq_mul_inv]
  ring

end NLS.KdV
