import NLS.SequenceSpaces.PositiveInsertion
import NLS.SequenceSpaces.DominatedCompactness

/-! Closed positive-index l2 sets with one coordinatewise l2 majorant
are norm compact, by literal insertion and restriction. -/
noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.LpSequence

theorem positiveRestriction_positiveInsert (d : lp (fun _ : ℕ+ => ℂ) 2) :
    positiveRestriction (positiveInsert d) = d := by
  ext m
  exact positiveInsert_apply d m

theorem isCompact_positive_of_isClosed_of_majorant
    (b : lp (fun _ : ℕ+ => ℂ) 2) (S : Set (lp (fun _ : ℕ+ => ℂ) 2))
    (hS : IsClosed S) (hb : ∀ d ∈ S, ∀ m, ‖d m‖ ≤ ‖b m‖) : IsCompact S := by
  let K : Set (Coeff 2) := {a | ∀ k : ℤ, ‖a k‖ ≤ ‖positiveInsert b k‖}
  have hK : IsClosed K := by
    simp only [K,ofPred_forall]
    exact isClosed_iInter (fun k => isClosed_le ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).continuous.norm) continuous_const)
  have hc := Coeff.isCompact_of_isClosed_of_majorant (by norm_num) (positiveInsert b) hK (fun _ ha => ha)
  apply (hc.image positiveRestrictionCLM.continuous).of_isClosed_subset hS
  intro d hd
  refine ⟨positiveInsert d,?_,positiveRestriction_positiveInsert d⟩
  intro k
  by_cases hk : 0 < k
  · let m : ℕ+ := ⟨k.toNat,by omega⟩
    have he : ((m:ℕ):ℤ) = k := Int.toNat_of_nonneg hk.le
    rw [← he,positiveInsert_apply,positiveInsert_apply]
    exact hb d hd m
  · rw [positiveInsert_apply_nonpos _ k (by omega),positiveInsert_apply_nonpos _ k (by omega)]

end NLS.LpSequence
