import NLS.KdV.HillMiuraLiftDerivative
import NLS.ZakharovShabat.SourcePhaseMonodromy

/-! The actual phase-rotated Dirac source for the Hill divisor.
Analyticity, the physical real form and the compact massive Fourier
principal remainder all hold for this SAME source, with its fixed phase. -/
noncomputable section
open Set NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

def rotatedDiracSource (P : HillProductEquationPatch) (q : PeriodOneHminusOne) : CoeffPair 2 :=
  sourcePhase (P.sourcePsi q)

theorem analytic_rotatedDiracSource (P : HillProductEquationPatch) :
    AnalyticOnNhd ℂ P.rotatedDiracSource P.source :=
  fun q hq => ((sourcePhase (p := 2)).analyticAt _).comp (P.analytic_sourcePsi q hq)

theorem isRealType_rotatedDiracSource (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    IsRealType (CoeffPair.toMax 2 (P.rotatedDiracSource q)) := by
  let B := P.parent.parent.miuraBall.actionBall
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  exact isRealType_sourcePhase (hillMiuraDiagonal u.val) (isRealType_hillMiuraDiagonal u)

theorem fderiv_rotatedDiracSource (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    fderiv ℂ P.rotatedDiracSource q=sourcePhase.comp (fderiv ℂ P.sourcePsi q) :=
  ((sourcePhase (p := 2)).hasFDerivAt.comp q (P.analytic_sourcePsi q hq).differentiableAt.hasFDerivAt).fderiv

theorem isCompactOperator_rotatedDiracSourceDerivative_sub_massInverse (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    IsCompactOperator (fderiv ℂ P.rotatedDiracSource q-
      (sourcePhase.comp hillMiuraDiagonal).comp (periodOneMassInverse 0)) := by
  rw [P.fderiv_rotatedDiracSource q hq]
  have he : sourcePhase.comp (fderiv ℂ P.sourcePsi q)-
      (sourcePhase.comp hillMiuraDiagonal).comp (periodOneMassInverse 0) =
      sourcePhase.comp (fderiv ℂ P.sourcePsi q-hillMiuraDiagonal.comp (periodOneMassInverse 0)) := by
    apply ContinuousLinearMap.ext
    intro h
    simp only [sub_apply,ContinuousLinearMap.comp_apply,map_sub]
  rw [he]
  exact (P.isCompactOperator_sourcePsiDerivative_sub_massInverse q hq).clm_comp sourcePhase

end NLS.KdV.HillProductEquationPatch
