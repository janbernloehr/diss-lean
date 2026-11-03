import NLS.KdV.HillDirichletAnalyticLabels
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem hillDirichletMultiplier_ofReal
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    (hillDirichletMultiplier q.val q.property.1 q.property.2 n hn : ℂ)=
      (-1 : ℂ)^n*hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn) := by
  rw [hillDirichletMultiplier,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
  congr 1
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im,hillL2DirichletSlope_real _ q.property.2]

theorem exists_hillDirichlet_norming_analytic_extension
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∃ a k : Coeff 2 → ℂ,
      AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val) ∧
      AnalyticAt ℂ k (SpectralWeight.one.toCoeff q.val) ∧
      a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) ∧
      k (SpectralWeight.one.toCoeff q.val)=(hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn : ℂ) ∧
      (∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val),
        hillL2DirichletCharacteristic p (a p)=0 ∧ exp (k p)=(-1 : ℂ)^n*hillL2DirichletSlope p (a p)) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        a (SpectralWeight.one.toCoeff p.val)=(hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ) ∧
        k (SpectralWeight.one.toCoeff p.val)=(hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn : ℂ) := by
  obtain ⟨a,ha,hax,hroot,hmatch⟩ := exists_hillDirichletEnergy_analytic_extension q n hn
  let M (p : Coeff 2) := (-1 : ℂ)^n*hillL2DirichletSlope p (a p)
  have hM : AnalyticAt ℂ M (SpectralWeight.one.toCoeff q.val) := by
    have hh := (analyticOnNhd_hillL2DirichletSlope_joint
      (a (SpectralWeight.one.toCoeff q.val),SpectralWeight.one.toCoeff q.val) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (a p,p)) (ha.prod analyticAt_id)
    exact analyticAt_const.mul hh
  have hM0 : M (SpectralWeight.one.toCoeff q.val)=
      (hillDirichletMultiplier q.val q.property.1 q.property.2 n hn : ℂ) := by
    dsimp only [M]
    rw [hax,← hillDirichletMultiplier_ofReal]
  have hslit : M (SpectralWeight.one.toCoeff q.val)∈slitPlane := by
    rw [hM0]
    exact Complex.ofReal_mem_slitPlane.mpr (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn)
  let k (p : Coeff 2) := log (M p)
  have hk : AnalyticAt ℂ k (SpectralWeight.one.toCoeff q.val) := hM.clog hslit
  have hk0 : k (SpectralWeight.one.toCoeff q.val)=
      (hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn : ℂ) := by
    dsimp only [k]
    rw [hM0,← Complex.ofReal_log (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn).le]
    rfl
  refine ⟨a,k,ha,hk,hax,hk0,?_,?_⟩
  · have hne : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val), M p≠0 :=
      hM.continuousAt.eventually_ne (slitPlane_ne_zero hslit)
    filter_upwards [hroot,hne] with p hp hnz
    exact ⟨hp,Complex.exp_log hnz⟩
  · filter_upwards [hmatch] with p hp
    refine ⟨hp,?_⟩
    change log (M (SpectralWeight.one.toCoeff p.val))=_
    have hm : M (SpectralWeight.one.toCoeff p.val)=
        (hillDirichletMultiplier p.val p.property.1 p.property.2 n hn : ℂ) := by
      dsimp only [M]
      rw [hp,← hillDirichletMultiplier_ofReal]
    rw [hm,← Complex.ofReal_log (hillDirichletMultiplier_pos p.val p.property.1 p.property.2 n hn).le]
    rfl

end NLS.KdV
