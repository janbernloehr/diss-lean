import NLS.KdV.HillL2Dirichlet
import NLS.MKdV.QuasiHillL2Sobolev
import NLS.KdV.HillMiuraL2Discriminant

/-! Exact comparison of the affine-energy L2 Dirichlet construction with
the independently normalized physical L2 Hill characteristic. -/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.Fourier NLS.LinearVolterra
open NLS.ZakharovShabat NLS.KdV
open scoped ContDiff ENNReal
namespace NLS.MKdV

theorem hillL2Dirichlet_miura_smooth (a : ScalarDomain 2) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (ha : ∀ n, a.val n = periodOneCoefficient f n) (μ : ℂ) :
    hillL2Dirichlet (sobolevMiuraHillPotential a) μ =
      quasiHillDirichlet (periodOneMiuraCurve a) μ := by
  have huf := periodOneSobolevSynthesis_eq_of_coefficients a f hf.continuous hp ha
  have hqf : ContDiff ℝ ∞ (miuraPotential f) :=
    (contDiff_infty_iff_deriv.mp hf).2.add (hf.pow 2)
  have hqp : Function.Periodic (miuraPotential f) 1 := by
    have hd := periodic_deriv_of_periodic f 1 hp
    intro x
    dsimp only [miuraPotential]
    rw [hd x,hp x]
  let b := SpectralWeight.one.toCoeff (smoothPeriodOneFourierData (miuraPotential f) hqf hqp)
  let Q := periodOneSynthesisCLM b
  have hQ (x : ℝ) : Q (x : AddCircle (2 : ℝ)) = miuraPotential f x :=
    congrFun (periodOneSynthesis_smoothPeriodOneFourierData (miuraPotential f) hqf hqp) x
  have hunit (n : ℤ) : sobolevMiuraUnitPotential a n = b n := by
    have h := sobolevMiuraUnitPotential_physical a n
    rw [huf] at h
    simpa only [b,SpectralWeight.toCoeff_apply,smoothPeriodOneFourierData_apply] using h
  have hcoef : sobolevMiuraHillPotential a = SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) := by
    ext k
    have hQk : fourierCoeff Q k = Coeff.periodDouble b k := by
      change fourierCoeff (continuousSynthesis (Coeff.periodDouble b)) k = _
      exact fourierCoeff_continuousSynthesis _ k
    simp only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,hQk,sobolevMiuraHillPotential]
    by_cases hk : k % 2 = 0
    · have he : k = 2*(k/2) := by omega
      rw [he,Coeff.periodDouble_even,Coeff.periodDouble_even]
      exact hunit _
    · have he : k = 2*(k/2)+1 := by omega
      rw [he,Coeff.periodDouble_odd,Coeff.periodDouble_odd]
  have hcurve : hillUnitPotentialCurve Q = miuraHillProfileCurve f (hf.of_le (by simp)) := by
    apply ContinuousMap.ext
    intro t
    exact hQ t
  have hU : periodOneMiuraCurve a = miuraProfileCurve f hf.continuous := by
    apply ContinuousMap.ext
    intro t
    exact (periodOneMiuraCurve_apply a t).trans (congrFun huf t)
  rw [hcoef,hillL2Dirichlet_eq_classical,hcurve,
    ← quasiHillDirichlet_profile_eq_classicalHill f (hf.of_le (by simp))]
  rw [hU]

/-- The exact physical characteristic comparison on every original complex H¹
input, at every complex energy, including zero. -/
theorem hillL2Dirichlet_miura (a : ScalarDomain 2) (μ : ℂ) :
    hillL2Dirichlet (sobolevMiuraHillPotential a) μ =
      quasiHillDirichlet (periodOneMiuraCurve a) μ := by
  have hL : Continuous (fun b : ScalarDomain 2 => hillL2Dirichlet (sobolevMiuraHillPotential b) μ) := by
    have hq : Continuous sobolevMiuraHillPotential :=
      continuous_iff_continuousAt.mpr (fun b => (analyticAt_sobolevMiuraHillPotential b).continuousAt)
    have hc : Continuous (fun p : ℂ × Coeff 2 => hillL2Dirichlet p.2 p.1) :=
      analyticOnNhd_hillL2Dirichlet_joint.continuous
    simpa only [Function.comp_def] using!
      (hc.comp (show Continuous (fun b : ScalarDomain 2 => (μ,sobolevMiuraHillPotential b)) from
        continuous_const.prodMk hq))
  have hU : Continuous periodOneMiuraCurve :=
    periodOneMiuraCurveCLM.continuous.congr (fun b => periodOneMiuraCurveCLM_apply b)
  have hcR : Continuous (fun p : ℂ × Curve ℂ => quasiHillDirichlet p.2 p.1) :=
    analyticOnNhd_quasiHillDirichlet_joint.continuous
  have hR : Continuous (fun b : ScalarDomain 2 => quasiHillDirichlet (periodOneMiuraCurve b) μ) := by
    simpa only [Function.comp_def] using!
      (hcR.comp (show Continuous (fun b : ScalarDomain 2 => (μ,periodOneMiuraCurve b)) from
        continuous_const.prodMk hU))
  have he := (WeightedCoeff.denseRange_ofFinsupp (Weight.sobolev 1) 2 (by simp)).equalizer hL hR (by
    funext b
    apply hillL2Dirichlet_miura_smooth _ (polynomial b) (contDiff_source_polynomial b)
      (periodic_source_polynomial b) _ μ
    intro n
    simp only [WeightedCoeff.ofFinsupp_apply,periodOneCoefficient_source_polynomial])
  exact congrFun he a


/-- Whenever a rough L2 Miura image is L2, its energy-affine Dirichlet
construction is exactly the actual physical Hill Dirichlet characteristic. -/
theorem quasiHillL2Dirichlet_eq_hillL2 (u q : Coeff 2)
    (himage : periodOneMiura u = periodOneL2Inclusion q) (lambda : ℂ) :
    quasiHillL2Dirichlet u lambda = hillL2Dirichlet (Coeff.periodDouble q) lambda := by
  let a : ScalarDomain 2 := ⟨u,periodOneMiura_memlp_sobolev_one u q himage⟩
  have ha : scalarInclusion a = u := by ext k; exact scalarInclusion_apply a k
  have hq : sobolevMiuraUnitPotential a = q := by
    ext k
    have h := congrArg (fun p : PeriodOneHminusOne => p.val k) himage
    rw [periodOneMiura_apply,periodOneL2Inclusion_apply] at h
    rw [sobolevMiuraUnitPotential_apply]
    exact h
  rw [← ha,quasiHillL2Dirichlet_scalarInclusion,← hillL2Dirichlet_miura,sobolevMiuraHillPotential,hq]

/-- A physical constant shift translates the energy with the exact scalar
Dirichlet normalization, without a zero-energy exception. -/
theorem quasiHillL2Dirichlet_eq_hillL2_of_shifted_image (u q : Coeff 2) (c lambda : ℂ)
    (himage : periodOneMiura u = periodOneL2Inclusion (q+lp.single 2 0 c)) :
    quasiHillL2Dirichlet u (lambda+c) = hillL2Dirichlet (Coeff.periodDouble q) lambda := by
  rw [quasiHillL2Dirichlet_eq_hillL2 u _ himage,map_add,periodDouble_single_zero,
    hillL2Dirichlet_add_const]

end NLS.MKdV
