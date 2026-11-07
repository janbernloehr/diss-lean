import NLS.KdV.HillPeriodOneL1Comparison
import NLS.KdV.ClassicalHillDirichletGradient
import NLS.Poisson.HminusGardnerBracket
import NLS.Fourier.FinitePeriodOneRealization
import NLS.Fourier.IntervalBilinearParseval

/-! ACTUAL H1 cotangents of the native H-minus-one Dirichlet characteristic, entire
in the native source. On every Wiener potential their original unit
Fourier coefficients equal the independently derived physical Dirichlet kernel. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.KdV

theorem analyticOnNhd_hillHminusDirichlet_source (μ : ℂ) :
    AnalyticOnNhd ℂ (fun q => hillHminusDirichlet q μ) univ := by
  intro q _
  exact (analyticOnNhd_hillHminusDirichlet_joint (μ,q) (mem_univ _)).comp
    (f := fun p : PeriodOneHminusOne => (μ,p)) (analyticAt_const.prod analyticAt_id)

def hillHminusDirichletGradient (μ : ℂ) (q : PeriodOneHminusOne) : WeightedCoeff (Weight.sobolev 1) 2 :=
  NLS.Poisson.hminusScalarGradient (fun p => hillHminusDirichlet p μ) q

theorem analyticOnNhd_hillHminusDirichletGradient (μ : ℂ) :
    AnalyticOnNhd ℂ (hillHminusDirichletGradient μ) univ :=
  NLS.Poisson.analyticOnNhd_hminusScalarGradient _ (analyticOnNhd_hillHminusDirichlet_source μ)

theorem fderiv_hillHminusDirichlet_potential_L1 (μ : ℂ) (a h : Coeff 1) :
    (fderiv ℂ (fun q => hillHminusDirichlet q μ) (periodOneL1Inclusion a)) (periodOneL1Inclusion h)=
      (fderiv ℂ (fun Q => classicalHillDirichlet Q μ) (periodOneL1PotentialCurve a)) (periodOneL1PotentialCurve h) := by
  have hN := (analyticOnNhd_hillHminusDirichlet_source μ (periodOneL1Inclusion a) (mem_univ _)).differentiableAt.hasFDerivAt
  let t : Icc (0:ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hCa : AnalyticAt ℂ (fun Q : Curve ℂ => classicalHillDirichlet Q μ) (periodOneL1PotentialCurve a) :=
    analyticAt_fst.comp (analyticOnNhd_classicalHillFlow_potential μ (0,1) t (periodOneL1PotentialCurve a) (mem_univ _))
  have hC := hCa.differentiableAt.hasFDerivAt
  have hn := (hN.comp a periodOneL1Inclusion.hasFDerivAt).fderiv
  have hc := (hC.comp a periodOneL1PotentialCurve.hasFDerivAt).fderiv
  have he : (fun b => hillHminusDirichlet (periodOneL1Inclusion b) μ)=
      fun b => classicalHillDirichlet (periodOneL1PotentialCurve b) μ :=
    funext (fun b => hillHminusDirichlet_eq_classical_L1 b μ)
  change fderiv ℂ (fun b => hillHminusDirichlet (periodOneL1Inclusion b) μ) a=_ at hn
  change fderiv ℂ (fun b => classicalHillDirichlet (periodOneL1PotentialCurve b) μ) a=_ at hc
  rw [he,hc] at hn
  have hh := congrArg (fun L : Coeff 1 →L[ℂ] ℂ => L h) hn
  simpa only [ContinuousLinearMap.comp_apply,Function.comp_def] using hh.symm

theorem hillHminusDirichletGradient_L1_coefficients (μ : ℂ) (a : Coeff 1) (k : ℤ) :
    (hillHminusDirichletGradient μ (periodOneL1Inclusion a)).val k=
      unitFourierCoefficient (classicalHillDirichletGradient (periodOneL1PotentialCurve a) μ) k := by
  rw [hillHminusDirichletGradient,NLS.Poisson.hminusScalarGradient_apply,
    ← periodOneL1Inclusion_ofFinsupp,fderiv_hillHminusDirichlet_potential_L1,
    fderiv_classicalHillDirichlet_eq_integral_gradient]
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x hx
  have hxi : x ∈ Icc (0:ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
  change extend (periodOneL1PotentialCurve (Coeff.ofFinsupp (Finsupp.single (-k) 1))) x*
    classicalHillDirichletGradient (periodOneL1PotentialCurve a) μ x=
    classicalHillDirichletGradient (periodOneL1PotentialCurve a) μ x*wave (-(2*k)) x
  rw [extend_coe _ ⟨x,hxi⟩,periodOneL1PotentialCurve_apply,periodOneSynthesis_ofFinsupp]
  rw [show polynomial (Finsupp.single (-k) 1) x=wave (-(2*k)) x by simp [polynomial]]
  ring

end NLS.KdV
