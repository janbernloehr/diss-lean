import NLS.SequenceSpaces.RealActionRotationOrbit
import NLS.SequenceSpaces.RealActionRotationProperties
import Mathlib.Topology.Connected.Basic

/-! # Connectedness of action tori in the sequence norm

Each finite sequence of coordinate rotations is joined to its starting
point by simultaneously scaling its angles. These curves make the finite
rotation orbit connected. Its norm closure is the entire action torus at
every finite Banach exponent, including infinitely many nonzero actions.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem continuous_scaledActionRotationSequence
    (moves : List (ℤ × ℝ)) (f : ℝ → RealCoeff p × RealCoeff p) (hf : Continuous f) :
    Continuous (fun t => actionRotationSequence (f t)
      (moves.map (fun move => (move.1,t*move.2)))) := by
  induction moves generalizing f with
  | nil => simpa only [List.map_nil,actionRotationSequence,List.foldl_nil] using hf
  | cons move moves ih =>
    simpa only [List.map_cons,actionRotationSequence,List.foldl_cons] using
      ih (fun t => actionRotation (f t) move.1 (t*move.2))
        ((continuous_actionRotation move.1).comp
          ((continuous_id.mul continuous_const).prodMk hf))

omit [Fact (1 ≤ p)] in
private theorem scaledActionRotationSequence_zero
    (moves : List (ℤ × ℝ)) (z : RealCoeff p × RealCoeff p) :
    actionRotationSequence z (moves.map (fun move => (move.1,(0 : ℝ)*move.2))) = z := by
  induction moves generalizing z with
  | nil => rfl
  | cons move moves ih =>
    simpa only [List.map_cons,actionRotationSequence,List.foldl_cons,zero_mul,
      actionRotation_zero] using ih z

/-- The finite coordinate-rotation orbit is connected in the actual sequence norm. -/
theorem isConnected_actionRotationSequence_range (z : RealCoeff p × RealCoeff p) :
    IsConnected (range (actionRotationSequence z)) := by
  refine ⟨⟨z,⟨[],rfl⟩⟩,?_⟩
  apply isPreconnected_of_forall z
  rintro y ⟨moves,rfl⟩
  let c : ℝ → RealCoeff p × RealCoeff p := fun t =>
    actionRotationSequence z (moves.map (fun move => (move.1,t*move.2)))
  refine ⟨range c,?_,⟨0,scaledActionRotationSequence_zero moves z⟩,⟨1,?_⟩,?_⟩
  · rintro y ⟨t,rfl⟩
    exact ⟨moves.map (fun move => (move.1,t*move.2)),rfl⟩
  · simp [c]
  · exact (isConnected_range
      (continuous_scaledActionRotationSequence moves (fun _ => z) continuous_const)).isPreconnected

/-- Every nonempty action torus based at a sequence is connected, even with infinite support. -/
theorem isConnected_actionTorus_self (hp : p ≠ ⊤) (z : RealCoeff p × RealCoeff p) :
    IsConnected (actionTorus p (pairAction z)) := by
  rw [← closure_actionRotationSequence_range hp z]
  exact (isConnected_actionRotationSequence_range z).closure

/-- Arbitrary action level sets are preconnected, allowing the empty case. -/
theorem isPreconnected_actionTorus (hp : p ≠ ⊤) (I : ℤ → ℝ) :
    IsPreconnected (actionTorus p I) := by
  rcases (actionTorus p I).eq_empty_or_nonempty with h | ⟨z,hz⟩
  · rw [h]
    exact isPreconnected_empty
  · have he : pairAction z = I := funext hz
    rw [← he]
    exact (isConnected_actionTorus_self hp z).isPreconnected

end NLS.RealCoeff
