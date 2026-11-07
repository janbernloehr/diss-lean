import NLS.KdV.HillAbelianUniformValueTail
import NLS.SequenceSpaces.PositiveSignedReciprocalSummability

/-! Absolute convergence of the ACTUAL physical off-index terms on
one open complex neighborhood before ALL n. The finite low terms need
no tail estimate, and every complex collapsed gap remains included. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_open_physicalOffIndex_absolute_summability (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∀ n : ℕ+, ∀ a ∈ U,
        Summable (fun m : ℕ+ => ‖if m = n then 0 else P.physicalOffIndexAbelianValue n m a‖) := by
  obtain ⟨U,hU,hqU,hUP,K,C,hC,hbound⟩ := P.exists_local_uniform_physicalOffIndexAbelianValue_tail_bound H q hq
  refine ⟨U,hU,hqU,hUP,?_⟩
  intro n a ha
  let gap := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a)
  let d := hillMiuraDirichletDisplacement (P.parent.parent.miuraBall.actionBall.lift a)-
    sourcePeriodicMidpointDisplacement (by norm_num) (by norm_num) (P.sourcePsi a)
  have hd (m : ℤ) : d m = P.physicalDirichletFrequency m a-
      sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) m := by
    simp only [d,lp.coeFn_sub,Pi.sub_apply,hillMiuraDirichletDisplacement_apply,
      sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint,physicalDirichletFrequency]
    ring
  apply Coeff.summable_norm_positive_of_signed_reciprocal_tail gap d n
    (fun m => if m = n then 0 else P.physicalOffIndexAbelianValue n m a) (by simp) K C hC.le
  intro m hm hmn
  simpa only [if_neg hmn,hd] using hbound a ha n m hm hmn

end NLS.KdV.HillProductEquationPatch
