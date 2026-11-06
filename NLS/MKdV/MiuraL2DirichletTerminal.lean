import NLS.KdV.HillL2DirichletTerminal
import NLS.MKdV.MiuraL2HillDirichlet
import NLS.MKdV.QuasiHillL2LagrangeIdentity

/-! The actual terminal quasi-derivative at a scalar Dirichlet root.
On physical L2 images it equals the independently normalized physical
terminal derivative. This comparison is the input for Miura-independent
Dirichlet norming data. -/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.Fourier NLS.LinearVolterra
open NLS.ZakharovShabat NLS.KdV
open scoped ContDiff ENNReal
namespace NLS.MKdV

/-- Terminal quasi-derivative of the actual normalized L2 Dirichlet state. -/
def quasiHillL2DirichletTerminal (u : Coeff 2) (lambda : ℂ) : ℂ :=
  (quasiHillL2SolutionCurve u lambda (0,1) ⟨1,by constructor <;> norm_num⟩).2

theorem analyticOnNhd_quasiHillL2DirichletTerminal_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => quasiHillL2DirichletTerminal p.2 p.1) univ := by
  intro p _
  have hs := analyticOnNhd_quasiHillL2SolutionCurve_joint (0,1) p (mem_univ _)
  have he : AnalyticAt ℂ (fun t : ℂ × Coeff 2 =>
      quasiHillL2SolutionCurve t.2 t.1 (0,1) ⟨1,by constructor <;> norm_num⟩) p :=
    ((ContinuousMap.evalCLM ℂ (⟨1,by constructor <;> norm_num⟩ : Icc (0:ℝ) 1) :
      Curve (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)).analyticAt _).comp hs
  exact analyticAt_snd.comp he

theorem quasiHillL2DirichletTerminal_ne_zero (u : Coeff 2) (lambda : ℂ)
    (hz : quasiHillL2Dirichlet u lambda = 0) :
    quasiHillL2DirichletTerminal u lambda ≠ 0 :=
  quasiHillL2Dirichlet_terminal_snd_ne_zero u lambda hz

theorem hillL2DirichletTerminal_miura_smooth (a : ScalarDomain 2) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (ha : ∀ n, a.val n = periodOneCoefficient f n) (μ : ℂ) :
    hillL2DirichletTerminal (sobolevMiuraHillPotential a) μ =
      periodOneMiuraCurve a ⟨1,by constructor <;> norm_num⟩*
        quasiHillL2Dirichlet (scalarInclusion a) μ+
          quasiHillL2DirichletTerminal (scalarInclusion a) μ := by
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
  rw [hcoef,hillL2DirichletTerminal_eq_classical,hcurve,
    quasiHillL2DirichletTerminal,quasiHillL2Dirichlet,
    quasiHillL2SolutionCurve_scalarInclusion,hU]
  have ht : (1:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have h := congrArg Prod.snd (physicalMiuraState_eq_classicalHillFlow
    (miuraProfileCurve f hf.continuous) f (fun _ => rfl)
    (show ContDiff ℝ 1 f from hf.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
    (miuraHillProfileCurve f (hf.of_le (by simp)))
    (Filter.Eventually.of_forall (fun x hx => by rw [extend_coe _ ⟨x,hx⟩]; rfl)) μ (0,1) ht)
  have hd := deriv_physicalMiuraSolution (miuraProfileCurve f hf.continuous) μ (0,1)
    ⟨1,by constructor <;> norm_num⟩
  simpa only [classicalHillDirichletTerminal,mul_zero,sub_zero] using h.symm.trans hd

/-- The physical derivative contains the usual endpoint gauge correction. -/
theorem hillL2DirichletTerminal_miura (a : ScalarDomain 2) (μ : ℂ) :
    hillL2DirichletTerminal (sobolevMiuraHillPotential a) μ =
      periodOneMiuraCurve a ⟨1,by constructor <;> norm_num⟩*
        quasiHillL2Dirichlet (scalarInclusion a) μ+
          quasiHillL2DirichletTerminal (scalarInclusion a) μ := by
  have hL : Continuous (fun b : ScalarDomain 2 => hillL2DirichletTerminal (sobolevMiuraHillPotential b) μ) := by
    have hq : Continuous sobolevMiuraHillPotential :=
      continuous_iff_continuousAt.mpr (fun b => (analyticAt_sobolevMiuraHillPotential b).continuousAt)
    have hc : Continuous (fun p : ℂ × Coeff 2 => hillL2DirichletTerminal p.2 p.1) :=
      analyticOnNhd_hillL2DirichletTerminal_joint.continuous
    simpa only [Function.comp_def] using!
      (hc.comp (show Continuous (fun b : ScalarDomain 2 => (μ,sobolevMiuraHillPotential b)) from
        continuous_const.prodMk hq))
  have hU : Continuous (fun b : ScalarDomain 2 => periodOneMiuraCurve b
      ⟨1,by constructor <;> norm_num⟩) :=
    (ContinuousMap.evalCLM ℂ (⟨1,by constructor <;> norm_num⟩ : Icc (0:ℝ) 1)).continuous.comp (periodOneMiuraCurveCLM.continuous.congr
      (fun b => periodOneMiuraCurveCLM_apply b))
  have hm : Continuous (fun b : ScalarDomain 2 => (μ,scalarInclusion b)) :=
    continuous_const.prodMk scalarInclusion.continuous
  have hD : Continuous (fun b : ScalarDomain 2 => quasiHillL2Dirichlet (scalarInclusion b) μ) := by
    have hc : Continuous (fun p : ℂ × Coeff 2 => quasiHillL2Dirichlet p.2 p.1) :=
      analyticOnNhd_quasiHillL2Dirichlet_joint.continuous
    simpa only [Function.comp_def] using hc.comp hm
  have hT : Continuous (fun b : ScalarDomain 2 => quasiHillL2DirichletTerminal (scalarInclusion b) μ) := by
    have hc : Continuous (fun p : ℂ × Coeff 2 => quasiHillL2DirichletTerminal p.2 p.1) :=
      analyticOnNhd_quasiHillL2DirichletTerminal_joint.continuous
    simpa only [Function.comp_def] using hc.comp hm
  have he := (WeightedCoeff.denseRange_ofFinsupp (Weight.sobolev 1) 2 (by simp)).equalizer
    hL ((hU.mul hD).add hT) (by
      funext b
      apply hillL2DirichletTerminal_miura_smooth _ (polynomial b) (contDiff_source_polynomial b)
        (periodic_source_polynomial b) _ μ
      intro n
      simp only [WeightedCoeff.ofFinsupp_apply,periodOneCoefficient_source_polynomial])
  exact congrFun he a

/-- At a Dirichlet root the endpoint gauge correction vanishes. -/
theorem quasiHillL2DirichletTerminal_eq_hillL2_of_root (u q : Coeff 2)
    (himage : periodOneMiura u = periodOneL2Inclusion q) (lambda : ℂ)
    (hz : quasiHillL2Dirichlet u lambda = 0) :
    quasiHillL2DirichletTerminal u lambda = hillL2DirichletTerminal (Coeff.periodDouble q) lambda := by
  let a : ScalarDomain 2 := ⟨u,periodOneMiura_memlp_sobolev_one u q himage⟩
  have ha : scalarInclusion a = u := by ext k; exact scalarInclusion_apply a k
  have hq : sobolevMiuraUnitPotential a = q := by
    ext k
    have h := congrArg (fun p : PeriodOneHminusOne => p.val k) himage
    rw [periodOneMiura_apply,periodOneL2Inclusion_apply] at h
    rw [sobolevMiuraUnitPotential_apply]
    exact h
  have he := hillL2DirichletTerminal_miura a lambda
  rw [ha,hz,mul_zero,zero_add,sobolevMiuraHillPotential,hq] at he
  exact he.symm

/-- The same terminal derivative is retained after the exact physical energy shift. -/
theorem quasiHillL2DirichletTerminal_eq_hillL2_of_shifted_root (u q : Coeff 2) (c lambda : ℂ)
    (himage : periodOneMiura u = periodOneL2Inclusion (q+lp.single 2 0 c))
    (hz : quasiHillL2Dirichlet u (lambda+c) = 0) :
    quasiHillL2DirichletTerminal u (lambda+c) = hillL2DirichletTerminal (Coeff.periodDouble q) lambda := by
  rw [quasiHillL2DirichletTerminal_eq_hillL2_of_root u _ himage _ hz,
    map_add,periodDouble_single_zero,hillL2DirichletTerminal_add_const]

end NLS.MKdV
