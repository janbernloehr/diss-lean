import NLS.KdV.HillNativeTraceFirstVariation
import NLS.KdV.HillMiuraGapMidpoints
import NLS.KdV.HminusOneCharacteristicOrder
import NLS.ZakharovShabat.SourcePeriodicIsospectral

/-! Every native mean-zero tangent at the free potential gives an ACTUAL
isospectral Dirac tangent through any valid local Miura lift. The shared
verified quadratic-factor stationarity controls symmetric coordinates,
including every collapsed free gap. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusMiuraActionBall

def diracSource (B : HillHminusMiuraActionBall) (q : PeriodOneHminusOne) : CoeffPair 2 :=
  hillMiuraDiagonal (B.lift q)

theorem analytic_diracSource (B : HillHminusMiuraActionBall) :
    AnalyticOnNhd ℂ B.diracSource B.source := by
  intro q hq
  exact (hillMiuraDiagonal.analyticAt (B.lift q)).comp
    (f := B.lift) (B.lift_analytic q hq)

theorem diracSource_real (B : HillHminusMiuraActionBall) (q : PeriodOneHminusOne)
    (hq : q ∈ B.source) (hr : IsRealPeriodOneHminusOne q) :
    IsRealType (CoeffPair.toMax 2 (B.diracSource q)) := by
  exact (hillMiuraRealSource ⟨B.lift q,B.lift_real q hq hr⟩).property

theorem diracSource_discriminant_eq (B : HillHminusMiuraActionBall) (q : PeriodOneHminusOne)
    (hq : q ∈ B.source) (z : ℂ) :
    canonicalDiscriminant (by norm_num) (periodOnePotential (B.diracSource q)) z =
      hillHminusDiscriminant q (z^2-(B.shift:ℂ)) :=
  (hillHminusDiscriminant_shifted_miura_square q (B.lift q) (B.shift:ℂ) z (B.image q hq)).symm

theorem fderiv_diracSource_free_isospectral (B : HillHminusMiuraActionBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (h : PeriodOneHminusOne) (hh : h.val 0=0) :
    SourceIsospectralDirection (by norm_num) (B.diracSource 0) ((fderiv ℂ B.diracSource 0) h) := by
  intro z
  let D : CoeffPair 2 → ℂ := fun ψ => canonicalDiscriminant (by norm_num) (periodOnePotential ψ) z
  have hD : DifferentiableAt ℂ D (B.diracSource 0) :=
    ((analyticOnNhd_canonicalDiscriminant_periodOne (by norm_num) (by norm_num)
      (z,B.diracSource 0) (mem_univ _)).comp
        (f := fun ψ : CoeffPair 2 => (z,ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hS := (B.analytic_diracSource 0 h0).differentiableAt
  have hc := (hD.hasFDerivAt.comp 0 hS.hasFDerivAt).fderiv
  change fderiv ℂ (fun q => D (B.diracSource q)) 0 = _ at hc
  have he : (fun q => D (B.diracSource q)) =ᶠ[𝓝 0]
      fun q => hillHminusDiscriminant q (z^2-(B.shift:ℂ)) := by
    filter_upwards [B.source_open.mem_nhds h0] with q hq
    exact B.diracSource_discriminant_eq q hq z
  rw [he.fderiv_eq] at hc
  have hv := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) hc
  change (fderiv ℂ (fun q => hillHminusDiscriminant q (z^2-(B.shift:ℂ))) 0) h =
    (fderiv ℂ D (B.diracSource 0)) ((fderiv ℂ B.diracSource 0) h) at hv
  change (fderiv ℂ D (B.diracSource 0)) ((fderiv ℂ B.diracSource 0) h)=0
  rw [← hv,fderiv_hillHminusDiscriminant_free_mean_zero h hh]

theorem fderiv_diracSource_free_symmetric_mean_zero (B : HillHminusMiuraActionBall)
    (h0 : (0 : PeriodOneHminusOne) ∈ B.source) (h : PeriodOneHminusOne) (hh : h.val 0=0) (n : ℤ) :
    (fderiv ℂ (fun q => sourceStandardRootMidpoint (by norm_num) (by norm_num) (B.diracSource q) n) 0) h=0 ∧
    (fderiv ℂ (fun q => (canonicalPeriodicGap (by norm_num) (by norm_num)
      (periodOnePotential (B.diracSource q)) (periodOnePotential_mem _) n)^2) 0) h=0 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hreal := B.diracSource_real 0 h0 hr
  have hi := B.fderiv_diracSource_free_isospectral h0 h hh
  have hv := fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero
    (by norm_num) (by norm_num) (B.diracSource 0) hreal _ hi n
  obtain ⟨W,_,_,hWreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap
    (p := 2) (by norm_num) (by norm_num)
  have ha := hMG (B.diracSource 0) (hWreal hreal) n
  have hS := (B.analytic_diracSource 0 h0).differentiableAt.hasFDerivAt
  have hm := (ha.1.differentiableAt.hasFDerivAt.comp 0 hS).fderiv
  have hg := (ha.2.differentiableAt.hasFDerivAt.comp 0 hS).fderiv
  constructor
  · change (fderiv ℂ (fun q => canonicalPeriodicMidpoint (by norm_num) (by norm_num)
      (periodOnePotential (B.diracSource q)) (periodOnePotential_mem _) n) 0) h=0
    have hm' := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) hm
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply] using hm'.trans hv.1
  · have hg' := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) hg
    simpa only [Function.comp_def,ContinuousLinearMap.comp_apply] using hg'.trans hv.2

end NLS.KdV.HillHminusMiuraActionBall
