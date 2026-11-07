import NLS.Articles.KdVPseudomeasures.OriginalLocalHillDifferentials
import NLS.KdV.HminusOneLocalHillEnergyCycles

/-! Local holomorphic differentials and literal normalized energy cycles
above EVERY original real mean-zero H-minus-one potential. The same
energy/source domain supports all indices and the preceding divisor
data. Global numerator independence, growth bounds and gluing remain
necessary for the global Hill differential construction. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem exists_original_local_Hill_energy_differentials :
    ∃ A : MiuraHillPsiFamily, ∀ q : OriginalHminusOnePotential,
      ∃ B : HillHminusDirichletBall,
        originalPeriodOneCoefficients q ∈ B.psiSource A ∧
        IsOpen (B.psiSource A) ∧ B.psiSource A ⊆ hillHminusCanonicalDirichletDomain ∧
        IsOpen (B.energyDomain A) ∧
        AnalyticOnNhd ℂ B.energyRoot (B.energyDomain A) ∧
        (∀ t ∈ B.energyDomain A, B.energyRoot t ≠ 0 ∧
          B.energyRoot t^2 = hillHminusRadicand t.2 t.1) ∧
        (∀ E : ℂ, (E,originalPeriodOneCoefficients q) ∈ B.energyDomain A →
          B.energyRoot (E,originalPeriodOneCoefficients q)^2 = (originalHillDiscriminant q E)^2-4) ∧
        (∀ n : ℕ+, AnalyticOnNhd ℂ (B.energyDifferential A n) (B.energyDomain A) ∧
          AnalyticOnNhd ℂ (hillHminusCanonicalDirichlet n) (B.psiSource A) ∧
          AnalyticOnNhd ℂ (hillHminusDirichletNorming n) (B.psiSource A) ∧
          AnalyticOnNhd ℂ (hillHminusDirichletSheet n) (B.psiSource A)) ∧
        ∀ a ∈ B.psiSource A, ∀ ha : IsRealPeriodOneHminusOne a, ∀ m : ℕ+,
          ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
            (hillMiuraDiagonal (B.miuraBall.actionBall.lift a)) ((m:ℕ):ℤ),
            0 < D.center-D.radius ∧
            let Γ := quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
              (B.miuraBall.actionBall.shift:ℂ)
            Γ.Inside {E | (E,a) ∈ B.energyDomain A} ∧
            Γ.windingIntegral (hillHminusLabels a ha (2*(m:ℕ)-1):ℂ) = 1 ∧
            Γ.windingIntegral (hillHminusLabels a ha (2*(m:ℕ)):ℂ) = 1 ∧
            ∀ n : ℕ+, (2*Real.pi:ℂ)⁻¹*Γ.integral
              (fun E => B.energyDifferential A n (E,a)) = if m = n then 1 else 0 := by
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  refine ⟨A,?_⟩
  intro q
  obtain ⟨B,hB⟩ := exists_local_hminusHillPsiFamily A _ (originalPeriodOneCoefficients_real q)
  have hsub := B.psiSource_subset_dirichletDomain A
  refine ⟨B,hB,B.psiSource_open A,hsub,B.energyDomain_open A,B.analytic_energyRoot A,?_,?_,?_,?_⟩
  · exact fun t ht => ⟨B.energyRoot_ne_zero A t ht,B.energyRoot_sq A t ht⟩
  · exact fun E hE => B.energyRoot_sq A (E,originalPeriodOneCoefficients q) hE
  · intro n
    exact ⟨B.analytic_energyDifferential A n,
      (analyticOnNhd_hillHminusCanonicalDirichlet n).mono hsub,
      (analyticOnNhd_hillHminusDirichletNorming n).mono hsub,
      (analyticOnNhd_hillHminusDirichletSheet n).mono hsub⟩
  · exact fun a ha hr m => B.exists_normalized_energyCircle A a ha hr m

end NLS.Articles.KdVPseudomeasures
