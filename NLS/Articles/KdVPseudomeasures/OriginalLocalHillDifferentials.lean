import NLS.Articles.KdVPseudomeasures.OriginalDirichletDivisor
import NLS.KdV.HminusOneLocalHillPsi

/-! Local analytic numerator and exact period input for the original KdV
angles, above EVERY original real mean-zero H-minus-one potential. This
is not yet a chart-independent global Hill differential or a Birkhoff map. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

/-- One verified psi family gives local all-index original H-minus-one numerator charts. -/
theorem exists_original_local_Hill_psi_families :
    ∃ A : MiuraHillPsiFamily, ∀ q : OriginalHminusOnePotential,
      ∃ B : HillHminusDirichletBall,
        originalPeriodOneCoefficients q ∈ B.psiSource A ∧ IsOpen (B.psiSource A) ∧
        B.psiSource A ⊆ hillHminusCanonicalDirichletDomain ∧
        (∀ a ∈ B.psiSource A, periodOneMiura (B.miuraBall.actionBall.lift a) =
          a+periodOneL2Inclusion (lp.single 2 0 (B.miuraBall.actionBall.shift:ℂ))) ∧
        (∀ a ∈ B.psiSource A, ∀ m : ℕ+,
          Nonempty (SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
            (hillMiuraDiagonal (B.miuraBall.actionBall.lift a)) ((m:ℕ):ℤ))) ∧
        ∀ n : ℕ+, AnalyticOnNhd ℂ (B.psiNumerator A n) (univ ×ˢ B.psiSource A) ∧
          AnalyticOnNhd ℂ (hillHminusCanonicalDirichlet n) (B.psiSource A) ∧
          AnalyticOnNhd ℂ (hillHminusDirichletNorming n) (B.psiSource A) ∧
          AnalyticOnNhd ℂ (hillHminusDirichletSheet n) (B.psiSource A) ∧
          ∀ a ∈ B.psiSource A, ∀ m : ℕ+,
            ∀ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
              (hillMiuraDiagonal (B.miuraBall.actionBall.lift a)) ((m:ℕ):ℤ),
              (2*Real.pi:ℂ)⁻¹*(∮ z in C((D.center:ℂ),D.radius),
                (2*z*B.psiNumerator A n (z^2-(B.miuraBall.actionBall.shift:ℂ),a))/
                  sourceCanonicalRoot (by norm_num) (by norm_num)
                    (hillMiuraDiagonal (B.miuraBall.actionBall.lift a)) z) = if m = n then 1 else 0 := by
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  refine ⟨A,?_⟩
  intro q
  obtain ⟨B,hB⟩ := exists_local_hminusHillPsiFamily A _ (originalPeriodOneCoefficients_real q)
  have hsub := B.psiSource_subset_dirichletDomain A
  refine ⟨B,hB,B.psiSource_open A,hsub,?_,?_,?_⟩
  · exact fun a ha => B.miuraBall.actionBall.image a ha.1
  · exact fun a ha m => B.nonempty_psiPeriodCircle A a ha m
  · intro n
    exact ⟨B.analytic_psiNumerator A n,(analyticOnNhd_hillHminusCanonicalDirichlet n).mono hsub,
      (analyticOnNhd_hillHminusDirichletNorming n).mono hsub,
      (analyticOnNhd_hillHminusDirichletSheet n).mono hsub,
      fun a ha m D => B.psiNumerator_pullback_period A n m a ha D⟩

end NLS.Articles.KdVPseudomeasures
