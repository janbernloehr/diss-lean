import NLS.KdV.HillNativeCotangents
import NLS.KdV.HillPhysicalFourierCoefficients
import NLS.Poisson.UnitIntervalBilinearPairing

/-! # Actual native Fréchet derivatives of independent Hill branches

Period doubling is applied to the potential, while the gradients retain
their literal unit Fourier coefficients. The result represents the
derivative on all complex L² variations, rather than only real directions.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.FunctionalAnalysis NLS.LinearVolterra NLS.Fourier NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem hasFDerivAt_hillUnit_pullback_of_curve (F : Coeff 2 → ℂ) (p r : Coeff 2)
    (hp : Coeff.periodDouble r = p) (D : PeriodOneH2CurveData)
    (hF : DifferentiableAt ℂ F p)
    (hgrad : ∀ h : Coeff 2, (fderiv ℂ F p) h =
      ∫ x in (0 : ℝ)..1,-(hillPhysicalDirection h).ofLp.2 x*extend D.profile x) :
    HasFDerivAt (fun b => F (Coeff.periodDouble b))
      (reflectedHilbertPairing (scalarInclusion D.inclusion)) r := by
  have hd : HasFDerivAt F (fderiv ℂ F p) (Coeff.periodDouble r) := by
    rw [hp]
    exact hF.hasFDerivAt
  have he : (fderiv ℂ F p).comp Coeff.periodDouble.toContinuousLinearMap =
      reflectedHilbertPairing (scalarInclusion D.inclusion) := by
    apply ContinuousLinearMap.ext
    intro h
    change (fderiv ℂ F p) (Coeff.periodDouble h) = _
    rw [hgrad,reflectedHilbertPairing_comm]
    exact (reflectedHilbertPairing_eq_unit_integral h (scalarInclusion D.inclusion)
      (fun x => -(hillPhysicalDirection (Coeff.periodDouble h)).ofLp.2 x) (extend D.profile)
      (Lp.memLp (hillPhysicalDirection (Coeff.periodDouble h)).ofLp.2).neg
      (memLp_unitCurve_extend 2 D.profile)
      (fun n => (periodOneCoefficient_hillPhysicalDirection_periodDouble h n).symm)
      (fun n => by rw [scalarInclusion_apply,D.inclusion_apply])).symm
  simpa only [Function.comp_def,he] using hd.comp r Coeff.periodDouble.toContinuousLinearMap.hasFDerivAt

theorem hasFDerivAt_hillDirichlet_unit_branch
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val) =
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p) = 0) :
    HasFDerivAt (fun b => a (Coeff.periodDouble b))
      (reflectedHilbertPairing (scalarInclusion (hillDirichletH2Data q n hn).inclusion))
      (Coeff.periodHalve (SpectralWeight.one.toCoeff q.val)) :=
  hasFDerivAt_hillUnit_pullback_of_curve a _ _
    ((Coeff.periodDouble_periodHalve _).trans ((Coeff.parityProjection_eq_self_iff 0 _).mpr q.property.1))
    (hillDirichletH2Data q n hn) ha.differentiableAt
    (hillDirichletGradient_represents_branch q n hn a ha ha0 hz)

theorem analyticAt_hillLogNorming_branch
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val) =
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)) :
    AnalyticAt ℂ (fun p => log ((-1 : ℂ)^n*hillL2DirichletSlope p (a p)))
      (SpectralWeight.one.toCoeff q.val) := by
  have hM : AnalyticAt ℂ (fun p => (-1 : ℂ)^n*hillL2DirichletSlope p (a p))
      (SpectralWeight.one.toCoeff q.val) := analyticAt_const.mul
    ((analyticOnNhd_hillL2DirichletSlope_joint
      (a (SpectralWeight.one.toCoeff q.val),SpectralWeight.one.toCoeff q.val) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (a p,p)) (ha.prod analyticAt_id))
  apply hM.clog
  rw [ha0,← hillDirichletMultiplier_ofReal]
  exact Complex.ofReal_mem_slitPlane.mpr (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn)

theorem hasFDerivAt_hillLogNorming_unit_branch
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2 → ℂ)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val) =
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), hillL2DirichletCharacteristic p (a p) = 0) :
    HasFDerivAt (fun b => log ((-1 : ℂ)^n*hillL2DirichletSlope (Coeff.periodDouble b) (a (Coeff.periodDouble b))))
      (reflectedHilbertPairing (scalarInclusion (hillLogNormingH2Data q n hn).inclusion))
      (Coeff.periodHalve (SpectralWeight.one.toCoeff q.val)) :=
  hasFDerivAt_hillUnit_pullback_of_curve _ _ _
    ((Coeff.periodDouble_periodHalve _).trans ((Coeff.parityProjection_eq_self_iff 0 _).mpr q.property.1))
    (hillLogNormingH2Data q n hn) (analyticAt_hillLogNorming_branch q n hn a ha ha0).differentiableAt
    (hillLogNormingGradient_represents_branch q n hn a ha ha0 hz)

end NLS.KdV
