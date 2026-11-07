import NLS.KdV.HillIntrinsicAngleBrackets
import NLS.KdV.HillAnglePairEndpointZero

/-! The branch-independent actual complete angle bracket vanishes
at every physical real source with all Dirichlet sheets zero, and
with its two selected ORIGINAL gaps open. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

theorem hillHminusCompletePhasePairBracket_eq_zero_at_all_endpoints (n m : ℕ+)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hn : hillHminusCanonicalGapSquare n q ≠ 0) (hm : hillHminusCanonicalGapSquare m q ≠ 0)
    (hterminal : ∀ j : ℕ+, hillHminusDirichletSheet j q=0) :
    hillHminusCompletePhasePairBracket n m q=0 := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  obtain ⟨C,_,hCq⟩ := exists_hillPhysicalOnIndexPhaseChart P n q (P.real_mem_physicalDirichletSource q hq hr) hr hn
  obtain ⟨D,_,hDq⟩ := exists_hillPhysicalOnIndexPhaseChart P m q (P.real_mem_physicalDirichletSource q hq hr) hr hm
  rw [(C.eventually_completePhasePairBracket_eq_local D q hCq hDq hr).eq_of_nhds]
  exact C.completePhasePairBracket_eq_zero_at_all_endpoints D q hCq hDq hr hterminal

end NLS.KdV
