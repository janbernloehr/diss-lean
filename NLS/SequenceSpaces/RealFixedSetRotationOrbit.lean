import NLS.SequenceSpaces.RealActionRotationOrbit

/-! # Finite rotations avoiding an arbitrary fixed index set

Equal-action pairs agreeing on a prescribed index set can be approximated by
finite rotations that never move a retained coordinate.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

/-- A finite replacement uses only indices outside the fixed index set. -/
theorem exists_rotationSequence_eqOn_avoiding_set (S : Set ℤ) (A : Finset ℤ)
    (z w : RealCoeff p × RealCoeff p)
    (h : ∀ n, pairAction z n = pairAction w n)
    (hh : ∀ n ∈ S, z.1 n = w.1 n ∧ z.2 n = w.2 n) :
    ∃ moves : List (ℤ × ℝ), (∀ move ∈ moves, move.1 ∉ S) ∧ ∀ n,
      (actionRotationSequence z moves).1 n = (if n ∈ A then w.1 n else z.1 n) ∧
      (actionRotationSequence z moves).2 n = (if n ∈ A then w.2 n else z.2 n) := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨[],by simp,fun n => by simp [actionRotationSequence]⟩
  | @insert k A hk ih =>
    obtain ⟨moves,hs,hm⟩ := ih
    by_cases hks : k ∈ S
    · refine ⟨moves,hs,fun n => ?_⟩
      by_cases hn : n = k
      · subst n
        simpa [hk,(hh k hks).1,(hh k hks).2] using hm k
      · simpa [hn] using hm n
    · obtain ⟨t,ht⟩ := exists_actionRotation_apply_eq (actionRotationSequence z moves) w k
        ((pairAction_actionRotationSequence z moves k).trans (h k))
      refine ⟨moves++[(k,t)],?_,fun n => ?_⟩
      · intro move hmove
        rcases List.mem_append.mp hmove with hmove | hmove
        · exact hs move hmove
        · simpa only [List.mem_singleton.mp hmove] using hks
      · simp only [actionRotationSequence,List.foldl_append,List.foldl_cons,List.foldl_nil]
        change (actionRotation (actionRotationSequence z moves) k t).1 n = _ ∧
          (actionRotation (actionRotationSequence z moves) k t).2 n = _
        by_cases hn : n = k
        · subst n
          simpa using ht
        · rw [(actionRotation_apply_ne _ k n hn t).1,(actionRotation_apply_ne _ k n hn t).2,
            (hm n).1,(hm n).2]
          simp [hn]

end NLS.RealCoeff
