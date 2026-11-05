import NLS.MKdV.QuasiHillDirichletCharacteristic
import NLS.KdV.HillL2DirichletCharacteristic
import NLS.MKdV.SobolevMiuraPotential
import NLS.MKdV.SobolevMiuraPrimitive
import NLS.MKdV.MiuraHillSpectralBridge
import NLS.KdV.HillL2EnergyDiscriminant
import NLS.ZakharovShabat.SobolevScalarSmoothDensity
import NLS.Fourier.PeriodOneFourierUniqueness

/-! # The original rough Hill Dirichlet characteristic on the full Miura domain

Physical scalar IVP uniqueness gives the identity on smooth profiles.
Continuity and H¹ density extend it to every original complex H¹ input,
including zero energy. No spectral zero or velocity is prescribed.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.Fourier NLS.LinearVolterra
open NLS.ZakharovShabat NLS.KdV
open scoped ContDiff ENNReal
namespace NLS.MKdV

theorem hillL2DirichletCharacteristic_miura_smooth (a : ScalarDomain 2) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (ha : ∀ n, a.val n = periodOneCoefficient f n) (μ : ℂ) :
    hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) μ =
      quasiHillDirichletCharacteristic (periodOneMiuraCurve a) μ := by
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
  rw [hcoef,hillL2DirichletCharacteristic_eq_classical,hcurve,hU]
  have hs := physicalMiuraState_eq_classicalHillFlow (miuraProfileCurve f hf.continuous) f
    (fun _ => rfl) (hf.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
    (miuraHillProfileCurve f (hf.of_le (by simp)))
    (Filter.Eventually.of_forall (fun x hx => by
      rw [extend_coe _ ⟨x,hx⟩]
      rfl)) μ (0,1) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  have hfirst := congrArg Prod.fst hs
  simpa only [physicalMiuraSolution,quasiHillDirichletCharacteristic,mul_zero,sub_zero] using hfirst.symm

/-- The exact physical operator comparison on every original complex H¹
input, at every complex energy, including zero. -/
theorem hillL2DirichletCharacteristic_miura (a : ScalarDomain 2) (μ : ℂ) :
    hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) μ =
      quasiHillDirichletCharacteristic (periodOneMiuraCurve a) μ := by
  have hL : Continuous (fun b : ScalarDomain 2 => hillL2DirichletCharacteristic (sobolevMiuraHillPotential b) μ) := by
    have hq : Continuous sobolevMiuraHillPotential :=
      continuous_iff_continuousAt.mpr (fun b => (analyticAt_sobolevMiuraHillPotential b).continuousAt)
    have hc : Continuous (fun p : ℂ × Coeff 2 => hillL2DirichletCharacteristic p.2 p.1) :=
      analyticOnNhd_hillL2DirichletCharacteristic_joint.continuous
    simpa only [Function.comp_def] using!
      (hc.comp (show Continuous (fun b : ScalarDomain 2 => (μ,sobolevMiuraHillPotential b)) from
        continuous_const.prodMk hq))
  have hU : Continuous periodOneMiuraCurve :=
    periodOneMiuraCurveCLM.continuous.congr (fun b => periodOneMiuraCurveCLM_apply b)
  have hcR : Continuous (fun p : ℂ × Curve ℂ => quasiHillDirichletCharacteristic p.2 p.1) :=
    analyticOnNhd_quasiHillDirichletCharacteristic_joint.continuous
  have hR : Continuous (fun b : ScalarDomain 2 => quasiHillDirichletCharacteristic (periodOneMiuraCurve b) μ) := by
    simpa only [Function.comp_def] using!
      (hcR.comp (show Continuous (fun b : ScalarDomain 2 => (μ,periodOneMiuraCurve b)) from
        continuous_const.prodMk hU))
  have he := (WeightedCoeff.denseRange_ofFinsupp (Weight.sobolev 1) 2 (by simp)).equalizer hL hR (by
    funext b
    apply hillL2DirichletCharacteristic_miura_smooth _ (polynomial b) (contDiff_source_polynomial b)
      (periodic_source_polynomial b) _ μ
    intro n
    simp only [WeightedCoeff.ofFinsupp_apply,periodOneCoefficient_source_polynomial])
  exact congrFun he a

end NLS.MKdV
