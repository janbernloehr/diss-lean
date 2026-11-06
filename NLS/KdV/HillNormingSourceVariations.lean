import NLS.KdV.HillDirichletHamiltonianSources
import NLS.KdV.HillDirichletAnalyticNorming
import NLS.KdV.HillPhysicalGermDerivativeUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- An actual physical log-norming germ with its nonzero Dirichlet-source derivative,
including at closed gaps and terminal endpoints. -/
theorem exists_hillLogNorming_dirichletSource_variations
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∃ F : Coeff 2 → ℂ, AnalyticAt ℂ F (SpectralWeight.one.toCoeff q.val) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        F (SpectralWeight.one.toCoeff p.val)=
          (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn : ℂ)) ∧
      ∀ k : ℕ, ∀ hk : 1≤k,
        (fderiv ℂ F (SpectralWeight.one.toCoeff q.val))
          (SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q k hk))=
            -(if n=k then (1/2 : ℂ) else 0) := by
  obtain ⟨a,ha,ha0,hzero,hmatch⟩ := exists_hillDirichletEnergy_analytic_extension q n hn
  let M : Coeff 2 → ℂ := fun p => (-1 : ℂ)^n*hillL2DirichletSlope p (a p)
  have hM : AnalyticAt ℂ M (SpectralWeight.one.toCoeff q.val) := by
    have hS := (analyticOnNhd_hillL2DirichletSlope_joint _ (mem_univ _)).comp
      (f := fun p : Coeff 2 => (a p,p)) (ha.prod analyticAt_id)
    exact analyticAt_const.mul hS
  have hM0 : M (SpectralWeight.one.toCoeff q.val)=
      (hillDirichletMultiplier q.val q.property.1 q.property.2 n hn : ℂ) := by
    dsimp only [M]
    rw [ha0,←hillDirichletMultiplier_ofReal]
  have hslit : M (SpectralWeight.one.toCoeff q.val)∈Complex.slitPlane := by
    rw [hM0]
    exact Complex.ofReal_mem_slitPlane.mpr (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn)
  let F : Coeff 2 → ℂ := fun p => Complex.log (M p)
  refine ⟨F,hM.clog hslit,?_,?_⟩
  · filter_upwards [hmatch] with p hp
    dsimp only [F,M]
    rw [hp,←hillDirichletMultiplier_ofReal,
      ←Complex.ofReal_log (hillDirichletMultiplier_pos p.val p.property.1 p.property.2 n hn).le]
    rfl
  · intro k hk
    exact hillDirichletLogBranch_dirichletHamiltonianSource_fderiv q n k hn hk a ha ha0 hzero

/-- The actual log-norming source derivative is intrinsic to its physical germ. -/
theorem hillLogNormingGerm_dirichletSource_fderiv
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (G : Coeff 2 → ℂ) (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q.val))
    (hGreal : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=
        (hillDirichletLogMultiplier p.val p.property.1 p.property.2 n hn : ℂ))
    (k : ℕ) (hk : 1≤k) :
    (fderiv ℂ G (SpectralWeight.one.toCoeff q.val))
      (SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q k hk))=
        -(if n=k then (1/2 : ℂ) else 0) := by
  obtain ⟨F,hF,hFreal,hFD⟩ := exists_hillLogNorming_dirichletSource_variations q n hn
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val)=F (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hGreal,hFreal] with p hpG hpF
    exact hpG.trans hpF.symm
  exact (hillPhysicalCoefficientGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2 G F hG hF heq
    (hillDirichletHamiltonianSource q k hk) (hillDirichletHamiltonianSource_mem_even q k hk)).trans (hFD k hk)

end NLS.KdV
