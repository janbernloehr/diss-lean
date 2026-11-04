import NLS.KdV.HillCanonicalPsiIsospectral
import NLS.KdV.HillPhysicalDirichletSheetCoefficient
import NLS.ZakharovShabat.SourceOmittedRootIsospectral
import NLS.ComplexAnalysis.StationaryScalarQuotient

/-! Stationarity of the actual symmetric spectral data and regular
Hill gap numerators in native isospectral directions. The infinite
omitted product is the actual verified product, including on the
selected gap and its endpoints. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

theorem fderiv_sourcePsi_isospectral (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) :
    SourceIsospectralDirection (by norm_num) (P.sourcePsi q) ((fderiv ℂ P.sourcePsi q) h) :=
  P.parent.parent.miuraBall.actionBall.fderiv_diracSource_isospectral q
    (P.parent.subset (P.subset hq)).1 h hiso

theorem fderiv_symmetric_isospectral_eq_zero (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) (m : ℤ) :
    (fderiv ℂ (fun a => sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) m) q) h = 0 ∧
      (fderiv ℂ (fun a => (canonicalPeriodicGap (by norm_num) (by norm_num)
        (periodOnePotential (P.sourcePsi a)) (periodOnePotential_mem _) m)^2) q) h = 0 := by
  have hv := fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero
    (by norm_num) (by norm_num) (P.sourcePsi q) (P.sourcePsi_real q hq hr) _
    (P.fderiv_sourcePsi_isospectral q hq h hiso) m
  obtain ⟨W,_,_,hRW,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap
    (p := 2) (by norm_num) (by norm_num)
  have ha := hMG (P.sourcePsi q) (hRW (P.sourcePsi_real q hq hr)) m
  have hS := (P.analytic_sourcePsi q hq).differentiableAt.hasFDerivAt
  have hm := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h)
    (ha.1.differentiableAt.hasFDerivAt.comp q hS).fderiv
  have hg := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h)
    (ha.2.differentiableAt.hasFDerivAt.comp q hS).fderiv
  constructor
  · simpa only [Function.comp_def,ContinuousLinearMap.comp_apply] using hm.trans hv.1
  · simpa only [Function.comp_def,ContinuousLinearMap.comp_apply] using hg.trans hv.2

theorem fderiv_abelianGapRootMultiplier_isospectral_eq_zero (P : HillProductEquationPatch)
    (m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0)
    (z : ℂ) (hz : z ∈ Metric.ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) :
    (fderiv ℂ (fun a => P.abelianGapRootMultiplier m (z,a)) q) h = 0 := by
  let O : CoeffPair 2 → ℂ := fun ψ => sourceStandardRootOmittedProduct
    (by norm_num) (by norm_num) ((m:ℕ):ℤ) ψ z
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _)
  have hzO := D.closedBall_subset_omittedDomain (Metric.ball_subset_closedBall hz)
  have hO : DifferentiableAt ℂ O (P.sourcePsi q) :=
    (((P.quotients.roots.joint ((m:ℕ):ℤ)).2 (z,P.sourcePsi q) ⟨(P.image q hq).1,hzO⟩).comp
      (f := fun ψ : CoeffPair 2 => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hc := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h)
    (hO.hasFDerivAt.comp q (P.analytic_sourcePsi q hq).differentiableAt.hasFDerivAt).fderiv
  have hozero := fderiv_sourceStandardRootOmittedProduct_isospectral_eq_zero
    (by norm_num) (by norm_num) (P.sourcePsi q) (P.sourcePsi_real q hq hr) _
    (P.fderiv_sourcePsi_isospectral q hq h hiso) ((m:ℕ):ℤ) z hzO
  have hzcomp : (fderiv ℂ (fun a => O (P.sourcePsi a)) q) h = 0 := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply] using hc.trans hozero
  change (fderiv ℂ (fun a => (2*I)*O (P.sourcePsi a)) q) h = 0
  have hd : DifferentiableAt ℂ (fun a => O (P.sourcePsi a)) q :=
    hO.comp q (P.analytic_sourcePsi q hq).differentiableAt
  rw [fderiv_const_mul hd]
  simp only [smul_apply,smul_eq_mul,hzcomp,mul_zero]

theorem fderiv_abelianFrequencyNumerator_isospectral_eq_zero (P : HillProductEquationPatch)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) (z : ℂ) :
    (fderiv ℂ (fun a => P.abelianFrequencyNumerator n (z,a)) q) h = 0 := by
  let E := z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)
  have hp : q ∈ hillHminusCanonicalPsiDomain := Set.mem_iUnion.mpr ⟨P.parent,P.subset hq⟩
  have hd : DifferentiableAt ℂ (fun a => hillHminusCanonicalPsi n (E,a)) q :=
    ((analyticOnNhd_hillHminusCanonicalPsi n (E,q) ⟨mem_univ _,hp⟩).comp
      (f := fun a : PeriodOneHminusOne => (E,a)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  change (fderiv ℂ (fun a => (2*z)*hillHminusCanonicalPsi n (E,a)) q) h = 0
  rw [fderiv_const_mul hd]
  simp only [smul_apply,smul_eq_mul,
    fderiv_hillHminusCanonicalPsi_isospectral_eq_zero_of_real n q hr h hiso E,mul_zero]

theorem fderiv_abelianGapNumerator_isospectral_eq_zero (P : HillProductEquationPatch)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0)
    (z : ℂ) (hz : z ∈ Metric.ball (P.centers ((m:ℕ):ℤ):ℂ) (P.radii ((m:ℕ):ℤ))) :
    (fderiv ℂ (fun a => P.abelianGapNumerator n m (z,a)) q) h = 0 := by
  have hn : DifferentiableAt ℂ (fun a => P.abelianFrequencyNumerator n (z,a)) q :=
    ((P.analytic_abelianFrequencyNumerator n (z,q) ⟨mem_univ _,hq⟩).comp
      (f := fun a : PeriodOneHminusOne => (z,a)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hk : DifferentiableAt ℂ (fun a => P.abelianGapRootMultiplier m (z,a)) q :=
    ((P.analytic_abelianGapRootMultiplier m (z,q) ⟨hz,hq⟩).comp
      (f := fun a : PeriodOneHminusOne => (z,a)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  exact fderiv_stationary_scalar_quotient _ _ q h hn hk
    (P.abelianGapRootMultiplier_ne_zero m (z,q) ⟨hz,hq⟩)
    (P.fderiv_abelianFrequencyNumerator_isospectral_eq_zero n q hq hr h hiso z)
    (P.fderiv_abelianGapRootMultiplier_isospectral_eq_zero m q hq hr h hiso z hz)

end NLS.KdV.HillProductEquationPatch
