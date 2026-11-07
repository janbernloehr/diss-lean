import NLS.KdV.HillNativeTraceFirstVariation
import NLS.KdV.ClassicalHillTraceGradient
import NLS.Poisson.HminusGardnerBracket
import NLS.Fourier.FinitePeriodOneRealization
import NLS.Fourier.IntervalBilinearParseval

/-! ACTUAL H1 cotangents of the native H-minus-one discriminant, entire
in the native source. On every Wiener potential their original unit
Fourier coefficients equal the independently derived physical trace kernel. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.KdV

theorem analyticOnNhd_hillHminusDiscriminant_source (μ : ℂ) :
    AnalyticOnNhd ℂ (fun q => hillHminusDiscriminant q μ) univ := by
  intro q _
  exact (analyticOnNhd_hillHminusDiscriminant_joint (μ,q) (mem_univ _)).comp
    (f := fun p : PeriodOneHminusOne => (μ,p)) (analyticAt_const.prod analyticAt_id)

def hillHminusDiscriminantGradient (μ : ℂ) (q : PeriodOneHminusOne) : WeightedCoeff (Weight.sobolev 1) 2 :=
  NLS.Poisson.hminusScalarGradient (fun p => hillHminusDiscriminant p μ) q

theorem analyticOnNhd_hillHminusDiscriminantGradient (μ : ℂ) :
    AnalyticOnNhd ℂ (hillHminusDiscriminantGradient μ) univ :=
  NLS.Poisson.analyticOnNhd_hminusScalarGradient _ (analyticOnNhd_hillHminusDiscriminant_source μ)

theorem fderiv_hillHminusDiscriminant_potential_L1 (μ : ℂ) (a h : Coeff 1) :
    (fderiv ℂ (fun q => hillHminusDiscriminant q μ) (periodOneL1Inclusion a)) (periodOneL1Inclusion h)=
      (fderiv ℂ (fun Q => classicalHillDiscriminant Q μ) (periodOneL1PotentialCurve a)) (periodOneL1PotentialCurve h) := by
  have hN := (analyticOnNhd_hillHminusDiscriminant_source μ (periodOneL1Inclusion a) (mem_univ _)).differentiableAt.hasFDerivAt
  have hC := ((analyticOnNhd_classicalHillDiscriminant_joint (μ,periodOneL1PotentialCurve a) (mem_univ _)).comp
    (f := fun Q : Curve ℂ => (μ,Q)) (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt
  have hn := (hN.comp a periodOneL1Inclusion.hasFDerivAt).fderiv
  have hc := (hC.comp a periodOneL1PotentialCurve.hasFDerivAt).fderiv
  have he : (fun b => hillHminusDiscriminant (periodOneL1Inclusion b) μ)=
      fun b => classicalHillDiscriminant (periodOneL1PotentialCurve b) μ :=
    funext (fun b => hillHminusDiscriminant_eq_classical_L1 b μ)
  change fderiv ℂ (fun b => hillHminusDiscriminant (periodOneL1Inclusion b) μ) a=_ at hn
  change fderiv ℂ (fun b => classicalHillDiscriminant (periodOneL1PotentialCurve b) μ) a=_ at hc
  rw [he,hc] at hn
  have hh := congrArg (fun L : Coeff 1 →L[ℂ] ℂ => L h) hn
  simpa only [ContinuousLinearMap.comp_apply,Function.comp_def] using hh.symm

theorem hillHminusDiscriminantGradient_L1_coefficients (μ : ℂ) (a : Coeff 1) (k : ℤ) :
    (hillHminusDiscriminantGradient μ (periodOneL1Inclusion a)).val k=
      unitFourierCoefficient (classicalHillTraceGradient (periodOneL1PotentialCurve a) μ) k := by
  rw [hillHminusDiscriminantGradient,NLS.Poisson.hminusScalarGradient_apply,
    ← periodOneL1Inclusion_ofFinsupp,fderiv_hillHminusDiscriminant_potential_L1,
    fderiv_classicalHillDiscriminant_eq_integral_gradient]
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x hx
  have hxi : x ∈ Icc (0:ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
  change extend (periodOneL1PotentialCurve (Coeff.ofFinsupp (Finsupp.single (-k) 1))) x*
    classicalHillTraceGradient (periodOneL1PotentialCurve a) μ x=
    classicalHillTraceGradient (periodOneL1PotentialCurve a) μ x*wave (-(2*k)) x
  rw [extend_coe _ ⟨x,hxi⟩,periodOneL1PotentialCurve_apply,periodOneSynthesis_ofFinsupp]
  rw [show polynomial (Finsupp.single (-k) 1) x=wave (-(2*k)) x by simp [polynomial]]
  ring

end NLS.KdV
