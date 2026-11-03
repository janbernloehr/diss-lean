import NLS.SequenceSpaces.RealTailRotationOrbit

/-! # Closed sets invariant under tail rotations contain complete tail tori

Finite rotations avoid the retained head. Their finite block replacements
converge in the full sequence norm, including infinitely many open modes.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Closed tail-rotation invariant sets contain every equal-action point
with the same finite head. No selected action must be nonzero. -/
theorem mem_of_isClosed_tail_rotation_invariant (hp : p ≠ ⊤)
    (S : Finset ℤ) (K : Set (RealCoeff p × RealCoeff p)) (hK : IsClosed K)
    (hrot : ∀ z ∈ K, ∀ k ∉ S, ∀ t : ℝ, actionRotation z k t ∈ K)
    (z : RealCoeff p × RealCoeff p) (hz : z ∈ K) (w : RealCoeff p × RealCoeff p)
    (ha : ∀ n, pairAction z n = pairAction w n)
    (hh : ∀ n ∈ S, z.1 n = w.1 n ∧ z.2 n = w.2 n) : w ∈ K := by
  have hmoves (moves : List (ℤ × ℝ)) (hs : ∀ move ∈ moves, move.1 ∉ S)
      (v : RealCoeff p × RealCoeff p) (hv : v ∈ K) : actionRotationSequence v moves ∈ K := by
    induction moves generalizing v with
    | nil => exact hv
    | cons move moves ih =>
      exact ih (fun m hm => hs m (List.mem_cons_of_mem _ hm)) _
        (hrot v hv move.1 (hs move (by simp)) move.2)
  apply hK.mem_of_tendsto (tendsto_splicePair hp z w)
  apply Eventually.of_forall
  intro A
  obtain ⟨moves,hs,hm⟩ := exists_tailRotationSequence_eqOn S A z w ha hh
  have he : actionRotationSequence z moves = splicePair z w A := by
    apply Prod.ext <;> ext n
    · exact (hm n).1.trans (splicePair_apply z w A n).1.symm
    · exact (hm n).2.trans (splicePair_apply z w A n).2.symm
  rw [← he]
  exact hmoves moves hs z hz

end NLS.RealCoeff
