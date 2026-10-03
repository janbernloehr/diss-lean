import NLS.SequenceSpaces.RealActionRotation
import NLS.SequenceSpaces.RealActionTorus
import NLS.SequenceSpaces.RealCoeffTruncation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Finite rotations are dense in every action torus

Equal-radius coordinate pairs differ by a rotation, also at radius zero.
Finite lists of rotations can therefore replace any finite block by the
corresponding block of a target with the same actions. These replacements
converge in the full sequence norm at every finite Banach exponent.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞}

/-- Any equal-action coordinate pair is reached by a single rotation. -/
theorem exists_actionRotation_apply_eq (z w : RealCoeff p × RealCoeff p) (k : ℤ)
    (hk : pairAction z k = pairAction w k) :
    ∃ t : ℝ, (actionRotation z k t).1 k = w.1 k ∧ (actionRotation z k t).2 k = w.2 k := by
  let a : ℂ := ⟨z.1 k,z.2 k⟩
  let b : ℂ := ⟨w.1 k,w.2 k⟩
  have hr : ‖a‖ = ‖b‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
    dsimp [a,b]
    dsimp [pairAction] at hk
    nlinarith
  refine ⟨b.arg-a.arg,?_,?_⟩
  · rw [(actionRotation_apply_same z k _).1]
    change Real.cos (b.arg-a.arg)*a.re-Real.sin (b.arg-a.arg)*a.im = b.re
    rw [← Complex.norm_mul_cos_arg a,← Complex.norm_mul_sin_arg a]
    calc
      _ = ‖a‖*Real.cos ((b.arg-a.arg)+a.arg) := by rw [Real.cos_add]; ring
      _ = b.re := by rw [sub_add_cancel,hr,Complex.norm_mul_cos_arg]
  · rw [(actionRotation_apply_same z k _).2]
    change Real.sin (b.arg-a.arg)*a.re+Real.cos (b.arg-a.arg)*a.im = b.im
    rw [← Complex.norm_mul_cos_arg a,← Complex.norm_mul_sin_arg a]
    calc
      _ = ‖a‖*Real.sin ((b.arg-a.arg)+a.arg) := by rw [Real.sin_add]; ring
      _ = b.im := by rw [sub_add_cancel,hr,Complex.norm_mul_sin_arg]

/-- Finite coordinate rotations in the supplied list order. -/
def actionRotationSequence (z : RealCoeff p × RealCoeff p) (moves : List (ℤ × ℝ)) :
    RealCoeff p × RealCoeff p :=
  moves.foldl (fun w move => actionRotation w move.1 move.2) z

theorem pairAction_actionRotationSequence (z : RealCoeff p × RealCoeff p)
    (moves : List (ℤ × ℝ)) (n : ℤ) :
    pairAction (actionRotationSequence z moves) n = pairAction z n := by
  induction moves generalizing z with
  | nil => rfl
  | cons move moves ih =>
    exact (ih (actionRotation z move.1 move.2)).trans (pairAction_actionRotation z move.1 n move.2)

/-- Finite rotations match any prescribed finite block of an equal-action target. -/
theorem exists_actionRotationSequence_eqOn (z w : RealCoeff p × RealCoeff p)
    (h : ∀ n, pairAction z n = pairAction w n) (A : Finset ℤ) :
    ∃ moves : List (ℤ × ℝ), ∀ n,
      (actionRotationSequence z moves).1 n = (if n ∈ A then w.1 n else z.1 n) ∧
      (actionRotationSequence z moves).2 n = (if n ∈ A then w.2 n else z.2 n) := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨[],fun n => by simp [actionRotationSequence]⟩
  | @insert k A hk ih =>
    obtain ⟨moves,hm⟩ := ih
    obtain ⟨t,ht⟩ := exists_actionRotation_apply_eq (actionRotationSequence z moves) w k
      ((pairAction_actionRotationSequence z moves k).trans (h k))
    refine ⟨moves++[(k,t)],fun n => ?_⟩
    simp only [actionRotationSequence,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change (actionRotation (actionRotationSequence z moves) k t).1 n = _ ∧
      (actionRotation (actionRotationSequence z moves) k t).2 n = _
    by_cases hn : n = k
    · subst n
      simpa using ht
    · rw [(actionRotation_apply_ne _ k n hn t).1,(actionRotation_apply_ne _ k n hn t).2,
        (hm n).1,(hm n).2]
      simp [hn]

/-- Replace the finite selected block, retaining the original tail. -/
def splicePair (z w : RealCoeff p × RealCoeff p) (A : Finset ℤ) :
    RealCoeff p × RealCoeff p := z+truncatePair A (w-z)

theorem splicePair_apply (z w : RealCoeff p × RealCoeff p) (A : Finset ℤ) (n : ℤ) :
    (splicePair z w A).1 n = (if n ∈ A then w.1 n else z.1 n) ∧
    (splicePair z w A).2 n = (if n ∈ A then w.2 n else z.2 n) := by
  change z.1 n+truncate A (w.1-z.1) n = _ ∧ z.2 n+truncate A (w.2-z.2) n = _
  rw [truncate_apply,truncate_apply]
  change z.1 n+(if n ∈ A then w.1 n-z.1 n else 0) = _ ∧
    z.2 n+(if n ∈ A then w.2 n-z.2 n else 0) = _
  split_ifs <;> constructor <;> ring

theorem splicePair_mem_actionRotationSequence_range (z w : RealCoeff p × RealCoeff p)
    (h : ∀ n, pairAction z n = pairAction w n) (A : Finset ℤ) :
    splicePair z w A ∈ range (actionRotationSequence z) := by
  obtain ⟨moves,hm⟩ := exists_actionRotationSequence_eqOn z w h A
  refine ⟨moves,?_⟩
  apply Prod.ext <;> ext n
  · exact (hm n).1.trans (splicePair_apply z w A n).1.symm
  · exact (hm n).2.trans (splicePair_apply z w A n).2.symm

variable [Fact (1 ≤ p)]

/-- Finite block replacements converge in the full norm. -/
theorem tendsto_splicePair (hp : p ≠ ⊤) (z w : RealCoeff p × RealCoeff p) :
    Tendsto (splicePair z w) atTop (𝓝 w) := by
  have hc : Tendsto (fun _ : Finset ℤ => z) atTop (𝓝 z) := tendsto_const_nhds
  have ht := hc.add (tendsto_truncatePair hp (w-z))
  have he : z+(w-z) = w := by abel
  rw [he] at ht
  exact ht

/-- The closure of the finite rotation orbit is exactly the entire action torus. -/
theorem closure_actionRotationSequence_range (hp : p ≠ ⊤) (z : RealCoeff p × RealCoeff p) :
    closure (range (actionRotationSequence z)) = actionTorus p (pairAction z) := by
  apply Subset.antisymm
  · apply closure_minimal _ (isClosed_actionTorus _)
    rintro _ ⟨moves,rfl⟩ n
    exact pairAction_actionRotationSequence z moves n
  · intro w hw
    apply isClosed_closure.mem_of_tendsto (tendsto_splicePair hp z w)
    exact Eventually.of_forall (fun A => subset_closure
      (splicePair_mem_actionRotationSequence_range z w (fun n => (hw n).symm) A))

end NLS.RealCoeff
