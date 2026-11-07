import NLS.KdV.HillActionDirichletContour
import NLS.KdV.HillMiuraFreeIsospectral
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! Genuine joint analytic Miura contour integrands in the native
H-minus-one source, with the fixed physical energy shift retained.
The root domain is an open pullback of the actual Dirac joint domain. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillHminusMiuraActionBall

def rootJointDomain (B : HillHminusMiuraActionBall) (W : Set (CoeffPair 2)) :
    Set (ℂ × PeriodOneHminusOne) :=
  (univ ×ˢ B.source) ∩ (fun t => (t.1,B.diracSource t.2)) ⁻¹'
    sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W

theorem isOpen_rootJointDomain (B : HillHminusMiuraActionBall) (W : Set (CoeffPair 2))
    (hW : IsOpen (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W)) :
    IsOpen (B.rootJointDomain W) := by
  have hmap : AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => (t.1,B.diracSource t.2))
      (univ ×ˢ B.source) := by
    intro t ht
    exact analyticAt_fst.prod ((B.analytic_diracSource t.2 ht.2).comp (f := Prod.snd) analyticAt_snd)
  exact hmap.continuousOn.isOpen_inter_preimage (isOpen_univ.prod B.source_open) hW

theorem analytic_rootJoint (B : HillHminusMiuraActionBall) (W : Set (CoeffPair 2))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct (by norm_num) (by norm_num))
      (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W)) :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne => sourceCanonicalRoot
      (by norm_num) (by norm_num) (B.diracSource t.2) t.1) (B.rootJointDomain W) := by
  intro t ht
  exact (hroot (t.1,B.diracSource t.2) ht.2).comp
    (f := fun s : ℂ × PeriodOneHminusOne => (s.1,B.diracSource s.2))
    (analyticAt_fst.prod ((B.analytic_diracSource t.2 ht.1.2).comp (f := Prod.snd) analyticAt_snd))

theorem analytic_actionCotangentIntegrand_joint (B : HillHminusMiuraActionBall)
    (W : Set (CoeffPair 2))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct (by norm_num) (by norm_num))
      (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W)) :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne =>
      hillMiuraActionCotangentIntegrand t.2 (B.lift t.2) (B.shift:ℂ) t.1) (B.rootJointDomain W) := by
  intro t ht
  have hL := (analyticOnNhd_hillHminusDiscriminantCotangent_joint
    (t.1^2-(B.shift:ℂ),t.2) (mem_univ _)).comp
      (f := fun s : ℂ × PeriodOneHminusOne => (s.1^2-(B.shift:ℂ),s.2))
      (((analyticAt_fst.pow 2).sub analyticAt_const).prod analyticAt_snd)
  exact (analyticAt_fst.div (B.analytic_rootJoint W hroot t ht)
    (sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num)
      (B.diracSource t.2) t.1 ht.2.2)).smul hL

theorem analytic_actionDirichletIntegrand_joint (B : HillHminusMiuraActionBall)
    (W : Set (CoeffPair 2))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct (by norm_num) (by norm_num))
      (sourceCanonicalRootJointDomain (by norm_num) (by norm_num) W)) (m : ℕ+) :
    AnalyticOnNhd ℂ (fun t : ℂ × PeriodOneHminusOne =>
      hillMiuraActionDirichletIntegrand m t.2 (B.lift t.2) (B.shift:ℂ) t.1)
      (B.rootJointDomain W ∩ (univ ×ˢ hillHminusCanonicalDirichletDomain)) := by
  intro t ht
  have hQ := (analyticOnNhd_hillHminusDirichletFilledQuotient m
    (t.1^2-(B.shift:ℂ),t.2) ⟨mem_univ _,ht.2.2⟩).comp
      (f := fun s : ℂ × PeriodOneHminusOne => (s.1^2-(B.shift:ℂ),s.2))
      (((analyticAt_fst.pow 2).sub analyticAt_const).prod analyticAt_snd)
  exact (analyticAt_fst.div (B.analytic_rootJoint W hroot t ht.1)
    (sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num)
      (B.diracSource t.2) t.1 ht.1.2.2)).mul hQ

end NLS.KdV.HillHminusMiuraActionBall
