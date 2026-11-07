import NLS.KdV.HillDirichletGardnerGradient
import NLS.KdV.ClassicalHillDirichletCommutation
import NLS.Poisson.GardnerIntegralCoefficients

/-! The ACTUAL native Dirichlet characteristics Gardner-commute at
every complex H-minus-one source and every complex energy pair.
The continuous-potential computation transfers by verified Wiener density. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.KdV

def hillHminusDirichletGardnerBracket (μ ν : ℂ) (q : PeriodOneHminusOne) : ℂ :=
  NLS.Poisson.gardnerBivector (hillHminusDirichletGradient μ q) (hillHminusDirichletGradient ν q)

theorem analyticOnNhd_hillHminusDirichletGardnerBracket (μ ν : ℂ) :
    AnalyticOnNhd ℂ (hillHminusDirichletGardnerBracket μ ν) univ :=
  NLS.Poisson.analyticOnNhd_gardnerBivector _ _
    (analyticOnNhd_hillHminusDirichletGradient μ) (analyticOnNhd_hillHminusDirichletGradient ν)

theorem hillHminusDirichletGardnerBracket_L1_eq_integral (a : Coeff 1) (μ ν : ℂ) :
    hillHminusDirichletGardnerBracket μ ν (periodOneL1Inclusion a)=
      ∫ x in (0:ℝ)..1, classicalHillDirichletGradient (periodOneL1PotentialCurve a) μ x*
        classicalHillDirichletGradientPrime (periodOneL1PotentialCurve a) ν x :=
  NLS.Poisson.gardnerBivector_eq_integral_of_coefficients
    (hillHminusDirichletGradient μ (periodOneL1Inclusion a))
    (hillHminusDirichletGradient ν (periodOneL1Inclusion a))
    (classicalHillDirichletGradient (periodOneL1PotentialCurve a) μ)
    (classicalHillDirichletGradient (periodOneL1PotentialCurve a) ν)
    (classicalHillDirichletGradientPrime (periodOneL1PotentialCurve a) ν)
    (continuous_classicalHillDirichletGradient (periodOneL1PotentialCurve a) μ)
    (continuous_classicalHillDirichletGradient (periodOneL1PotentialCurve a) ν)
    (continuous_classicalHillDirichletGradientPrime (periodOneL1PotentialCurve a) ν)
    (fun t ht => hasDerivAt_classicalHillDirichletGradient (periodOneL1PotentialCurve a) ν ⟨t,ht.1.le,ht.2.le⟩)
    (classicalHillDirichletGradient_boundary (periodOneL1PotentialCurve a) ν)
    (hillHminusDirichletGradient_L1_coefficients μ a) (hillHminusDirichletGradient_L1_coefficients ν a)

theorem hillHminusDirichletGardnerBracket_L1_eq_zero (a : Coeff 1) (μ ν : ℂ) :
    hillHminusDirichletGardnerBracket μ ν (periodOneL1Inclusion a)=0 := by
  rw [hillHminusDirichletGardnerBracket_L1_eq_integral]
  exact integral_classicalHillDirichletGradients_eq_zero _ μ ν

theorem hillHminusDirichletGardnerBracket_eq_zero (q : PeriodOneHminusOne) (μ ν : ℂ) :
    hillHminusDirichletGardnerBracket μ ν q=0 :=
  denseRange_periodOneL1Inclusion.induction_on q
    (p := fun a : PeriodOneHminusOne => hillHminusDirichletGardnerBracket μ ν a=0)
    (isClosed_eq (analyticOnNhd_hillHminusDirichletGardnerBracket μ ν).continuous continuous_const)
    (fun a => hillHminusDirichletGardnerBracket_L1_eq_zero a μ ν)

theorem hillHminusDirichletCharacteristics_Gardner_commute (q : PeriodOneHminusOne) (μ ν : ℂ) :
    NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDirichlet p μ) (fun p => hillHminusDirichlet p ν) q=0 :=
  hillHminusDirichletGardnerBracket_eq_zero q μ ν

end NLS.KdV
