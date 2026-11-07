import NLS.KdV.HillOnIndexRemainderIsospectral
import NLS.KdV.HillOnIndexPhysicalCorrection
import NLS.ComplexAnalysis.MovingQuadraticSheetTerminalFDeriv

/-! The actual diagonal correction has the cleared moving-terminal
variation with its diagonal i term retained. Physical sheets may
vanish, and collapsed gaps are included. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem fderiv_physicalOnIndexAbelianCorrection_isospectral_frequency_cleared
    (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource)
    (hr : IsRealPeriodOneHminusOne q) (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) :
    hillHminusDirichletSheet n q*((fderiv ℂ (P.physicalOnIndexAbelianCorrection n) q) h) =
      P.abelianGapRootMultiplier n (P.physicalDirichletFrequency ((n:ℕ):ℤ) q,q)*
        (P.abelianGapNumerator n n (P.physicalDirichletFrequency ((n:ℕ):ℤ) q,q)-I)*
          ((fderiv ℂ (P.physicalDirichletFrequency ((n:ℕ):ℤ)) q) h) := by
  let μ := P.physicalDirichletFrequency ((n:ℕ):ℤ)
  let H := P.onIndexAbelianFilledRemainder n
  let M : PeriodOneHminusOne → ℂ := fun a => sourceStandardRootMidpoint
    (by norm_num) (by norm_num) (P.sourcePsi a) ((n:ℕ):ℤ)
  let G : PeriodOneHminusOne → ℂ := fun a => (canonicalPeriodicGap (by norm_num) (by norm_num)
    (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) ((n:ℕ):ℤ))^2
  let δ := hillHminusDirichletSheet n
  let K : PeriodOneHminusOne → ℂ := fun a => P.abelianGapRootMultiplier n (μ a,a)
  have hdisc : μ q ∈ ball (P.centers ((n:ℕ):ℤ):ℂ) (P.radii ((n:ℕ):ℤ)) :=
    P.physicalDirichletFrequency_mem_disc q hq _
  have hμ := (P.analytic_physicalDirichletFrequency ((n:ℕ):ℤ) q hq.1).differentiableAt
  have hH := (P.analytic_onIndexAbelianFilledRemainder n (μ q,q) ⟨hdisc,hq.1⟩).differentiableAt
  have hM : DifferentiableAt ℂ M q :=
    (P.parent.parent.miuraBall.midpoint_analytic ((n:ℕ):ℤ) q
      (P.parent.subset (P.subset hq.1)).1).differentiableAt
  have hG : DifferentiableAt ℂ G q :=
    (P.parent.parent.miuraBall.dirac_gap_square_analytic ((n:ℕ):ℤ) q
      (P.parent.subset (P.subset hq.1)).1).differentiableAt
  have hδ := (analyticOnNhd_hillHminusDirichletSheet n q (P.source_subset_canonicalDirichlet hq.1)).differentiableAt
  have hK : DifferentiableAt ℂ K q :=
    (P.analytic_abelianGapRootMultiplier n (μ q,q) ⟨hdisc,hq.1⟩).differentiableAt.comp q
      (f := fun a : PeriodOneHminusOne => (μ a,a)) (hμ.prodMk differentiableAt_id)
  have hKne : K q ≠ 0 := P.abelianGapRootMultiplier_ne_zero n (μ q,q) ⟨hdisc,hq.1⟩
  have hsq : (fun a => δ a^2) =ᶠ[𝓝 q] (fun a => K a^2*((μ a-M a)^2-G a/4)) := by
    filter_upwards [P.physicalDirichletSource_open.mem_nhds hq] with a ha
    have hd := P.physicalDirichletFrequency_mem_disc a ha ((n:ℕ):ℤ)
    have hk : K a ≠ 0 := P.abelianGapRootMultiplier_ne_zero n (μ a,a) ⟨hd,ha.1⟩
    have hs := P.physicalDirichletRootCoefficient_sq n a ha
    change (δ a/K a)^2 = (μ a-M a)^2-G a/4 at hs
    rw [div_pow] at hs
    have he := (div_eq_iff (pow_ne_zero 2 hk)).mp hs
    linear_combination he
  exact fderiv_moving_quadratic_sheet_terminal_cleared H μ M G δ K
    (P.physicalOnIndexAbelianCorrection n) q h (P.abelianGapNumerator n n (μ q,q)-I)
    hH hμ hM hG hδ hK hKne
    (P.fderiv_symmetric_isospectral_eq_zero q hq.1 hr h hiso ((n:ℕ):ℤ))
    (P.fderiv_onIndexAbelianFilledRemainder_isospectral_eq_zero n q hq.1 hr h hiso (μ q) hdisc)
    hsq (Filter.Eventually.of_forall (fun _ => rfl))
    (P.onIndexAbelianFilledRemainder_equation n q hq.1 (μ q) hdisc)

end NLS.KdV.HillProductEquationPatch
