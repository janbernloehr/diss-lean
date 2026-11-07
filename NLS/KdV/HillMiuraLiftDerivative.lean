import NLS.KdV.HillProductEquationPatches
import NLS.SequenceSpaces.PeriodOneMiuraLiftDerivative

/-! Actual Hill Miura charts have invertible full complex lift
derivatives, with the explicit massive principal part modulo compact
operators. The actual Dirac source derivative has the corresponding
compact remainder. No Poisson structures are identified here. -/
noncomputable section
open Set Filter Topology
namespace NLS.KdV.HillHminusMiuraActionBall

theorem eventually_lift_Miura_identity (B : HillHminusMiuraActionBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    (fun a => periodOneMiura (B.lift a)) =ᶠ[𝓝 q]
      (fun a => a+periodOneL2Inclusion (lp.single 2 0 (B.shift:ℂ))) := by
  filter_upwards [B.source_open.mem_nhds hq] with a ha
  exact B.image a ha

def liftDerivativeEquiv (B : HillHminusMiuraActionBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) : PeriodOneHminusOne ≃L[ℂ] Coeff 2 :=
  periodOneMiuraLiftDerivativeEquiv B.lift
    (periodOneL2Inclusion (lp.single 2 0 (B.shift:ℂ))) q
    (B.lift_analytic q hq) (B.eventually_lift_Miura_identity q hq)

theorem liftDerivativeEquiv_toCLM (B : HillHminusMiuraActionBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    (B.liftDerivativeEquiv q hq).toContinuousLinearMap=fderiv ℂ B.lift q := rfl

theorem liftDerivativeEquiv_symm_toCLM (B : HillHminusMiuraActionBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    (B.liftDerivativeEquiv q hq).symm.toContinuousLinearMap=periodOneMiuraLinearization (B.lift q) := rfl

theorem isCompactOperator_liftDerivative_sub_massInverse (B : HillHminusMiuraActionBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    IsCompactOperator (fderiv ℂ B.lift q-periodOneMassInverse 0) :=
  isCompactOperator_fderiv_Miura_lift_sub_massInverse B.lift
    (periodOneL2Inclusion (lp.single 2 0 (B.shift:ℂ))) q
    (B.lift_analytic q hq) (B.eventually_lift_Miura_identity q hq)

theorem eventually_lift_left_inverse (B : HillHminusMiuraActionBall)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    ∀ᶠ v in 𝓝 (B.lift q), B.lift
      (periodOneMiura v-periodOneL2Inclusion (lp.single 2 0 (B.shift:ℂ)))=v :=
  eventually_Miura_lift_left_inverse B.lift
    (periodOneL2Inclusion (lp.single 2 0 (B.shift:ℂ))) q
    (B.lift_analytic q hq) (B.eventually_lift_Miura_identity q hq)

end NLS.KdV.HillHminusMiuraActionBall
namespace NLS.KdV.HillProductEquationPatch

theorem fderiv_sourcePsi_eq_lift_comp (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    fderiv ℂ P.sourcePsi q=hillMiuraDiagonal.comp
      (fderiv ℂ P.parent.parent.miuraBall.actionBall.lift q) := by
  exact (hillMiuraDiagonal.hasFDerivAt.comp q
    (P.parent.parent.miuraBall.actionBall.lift_analytic q
      (P.parent.subset (P.subset hq)).1).differentiableAt.hasFDerivAt).fderiv

theorem isCompactOperator_sourcePsiDerivative_sub_massInverse (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) :
    IsCompactOperator (fderiv ℂ P.sourcePsi q-hillMiuraDiagonal.comp (periodOneMassInverse 0)) := by
  rw [P.fderiv_sourcePsi_eq_lift_comp q hq]
  have he : hillMiuraDiagonal.comp (fderiv ℂ P.parent.parent.miuraBall.actionBall.lift q)-
      hillMiuraDiagonal.comp (periodOneMassInverse 0) =
      hillMiuraDiagonal.comp (fderiv ℂ P.parent.parent.miuraBall.actionBall.lift q-periodOneMassInverse 0) := by
    apply ContinuousLinearMap.ext
    intro h
    simp only [sub_apply,ContinuousLinearMap.comp_apply,map_sub]
  rw [he]
  exact (P.parent.parent.miuraBall.actionBall.isCompactOperator_liftDerivative_sub_massInverse q
    (P.parent.subset (P.subset hq)).1).clm_comp hillMiuraDiagonal

end NLS.KdV.HillProductEquationPatch
