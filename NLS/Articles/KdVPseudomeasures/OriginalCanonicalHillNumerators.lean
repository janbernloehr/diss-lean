import NLS.Articles.KdVPseudomeasures.OriginalHillEnergyDifferentials
import NLS.KdV.HminusOneCanonicalHillPsiProperties

/-! Intrinsic original Hill energy numerators on ONE open connected
complex H-minus-one neighborhood containing EVERY original real source.
Different physical shifts and psi families now agree unconditionally.
This is a necessary normalized-differential input for source3.2(ii),
not the Hill product theorem, the angle construction or a Birkhoff map. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_common_analytic_Hill_numerators :
    IsOpen hillHminusCanonicalPsiDomain ∧ IsConnected hillHminusCanonicalPsiDomain ∧
    hillHminusCanonicalPsiDomain ⊆ hillHminusCanonicalDirichletDomain ∧
    (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ hillHminusCanonicalPsiDomain) ∧
    ∀ n : ℕ+, AnalyticOnNhd ℂ (hillHminusCanonicalPsi n) (univ ×ˢ hillHminusCanonicalPsiDomain) ∧
      AnalyticOnNhd ℂ (hillHminusCanonicalDirichlet n) hillHminusCanonicalPsiDomain ∧
      AnalyticOnNhd ℂ (hillHminusDirichletNorming n) hillHminusCanonicalPsiDomain ∧
      AnalyticOnNhd ℂ (hillHminusDirichletSheet n) hillHminusCanonicalPsiDomain := by
  have hs := hillHminusCanonicalPsiDomain_subset_dirichletDomain
  exact ⟨isOpen_hillHminusCanonicalPsiDomain,isConnected_hillHminusCanonicalPsiDomain,hs,
    fun q => real_mem_hillHminusCanonicalPsiDomain _ (originalPeriodOneCoefficients_real q),
    fun n => ⟨analyticOnNhd_hillHminusCanonicalPsi n,(analyticOnNhd_hillHminusCanonicalDirichlet n).mono hs,
      (analyticOnNhd_hillHminusDirichletNorming n).mono hs,(analyticOnNhd_hillHminusDirichletSheet n).mono hs⟩⟩

/-- No equal-shift or extra common-period hypothesis is required. -/
theorem original_Hill_numerators_eq_on_real_overlap
    (A D : MiuraHillPsiFamily) (B C : HillHminusDirichletBall) (q : OriginalHminusOnePotential)
    (hq : originalPeriodOneCoefficients q ∈ B.source ∩ C.source) (n : ℕ+) (E : ℂ) :
    B.psiNumerator A n (E,originalPeriodOneCoefficients q) =
      C.psiNumerator D n (E,originalPeriodOneCoefficients q) :=
  B.psiNumerator_eq_of_real_overlap C A D _ hq.1 hq.2 (originalPeriodOneCoefficients_real q) n E

/-- Above each original source, one actual chart and cycle family serve ALL indices. -/
theorem exists_original_intrinsic_Hill_energy_periods (q : OriginalHminusOnePotential) :
    ∃ B : HillHminusPsiBall, originalPeriodOneCoefficients q ∈ B.source ∧
      B.source ⊆ hillHminusCanonicalPsiDomain ∧
      (∀ n : ℕ+, ∀ E : ℂ, EqOn (fun a => hillHminusCanonicalPsi n (E,a))
        (fun a => B.numerator n (E,a)) B.source) ∧
      ∀ m : ℕ+, ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
        (hillMiuraDiagonal (B.parent.miuraBall.actionBall.lift (originalPeriodOneCoefficients q))) ((m:ℕ):ℤ),
        0 < D.center-D.radius ∧
        let Γ := quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
          (B.parent.miuraBall.actionBall.shift:ℂ)
        Γ.Inside {E | (E,originalPeriodOneCoefficients q) ∈ B.parent.energyDomain B.family} ∧
        Γ.windingIntegral (hillHminusLabels _ (originalPeriodOneCoefficients_real q) (2*(m:ℕ)-1):ℂ) = 1 ∧
        Γ.windingIntegral (hillHminusLabels _ (originalPeriodOneCoefficients_real q) (2*(m:ℕ)):ℂ) = 1 ∧
        ∀ n : ℕ+, (2*Real.pi:ℂ)⁻¹*Γ.integral
          (fun E => hillHminusCanonicalPsi n (E,originalPeriodOneCoefficients q)/
            B.parent.energyRoot (E,originalPeriodOneCoefficients q)) = if m = n then 1 else 0 := by
  obtain ⟨B,hB,hs,he⟩ := exists_hillHminusCanonicalPsi_local_presentation _
    (real_mem_hillHminusCanonicalPsiDomain _ (originalPeriodOneCoefficients_real q))
  exact ⟨B,hB,hs,he,fun m => B.exists_canonical_normalized_energyCircle _ hB (originalPeriodOneCoefficients_real q) m⟩

end NLS.Articles.KdVPseudomeasures
