import NLS.SequenceSpaces.ClosedFixedSetRotationSaturation

/-! # Positive coordinates determine negative coordinates on fixed action tori

A continuous map reversing rotations and reflecting their indices has
fixed points whose negative coordinates are determined by their positive
coordinates and actions. The central coordinate is left unrestricted.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On a fixed action torus, fixed points of a rotation-reflecting map
with the same positive coordinate pairs have the same negative pairs. -/
theorem negative_coordinates_eq_of_reflection_fixed (hp : p ≠ ⊤)
    (Q : (RealCoeff p × RealCoeff p) → (RealCoeff p × RealCoeff p)) (hQ : Continuous Q)
    (hrot : ∀ z k t, Q (actionRotation z k t) = actionRotation (Q z) (-k) (-t))
    (z w : RealCoeff p × RealCoeff p) (hz : Q z = z) (hw : Q w = w)
    (ha : ∀ n, pairAction z n = pairAction w n)
    (hpos : ∀ n : ℤ, 0 < n → z.1 n = w.1 n ∧ z.2 n = w.2 n)
    (n : ℤ) (hn : n < 0) : w.1 n = z.1 n ∧ w.2 n = z.2 n := by
  let S : Set ℤ := {k | 0 < k}
  let K : Set (RealCoeff p × RealCoeff p) :=
    {v | ∀ k : ℤ, ∀ _hk : k < 0, (Q v).1 k = z.1 k ∧ (Q v).2 k = z.2 k}
  have hK : IsClosed K := by
    simp only [K,ofPred_forall]
    apply isClosed_iInter
    intro k
    apply isClosed_iInter
    intro _hk
    exact (isClosed_eq (((lp.evalCLM ℝ (fun _ : ℤ => ℝ) p k).continuous.comp continuous_fst).comp hQ)
      continuous_const).inter
      (isClosed_eq (((lp.evalCLM ℝ (fun _ : ℤ => ℝ) p k).continuous.comp continuous_snd).comp hQ)
        continuous_const)
  have hKrot : ∀ v ∈ K, ∀ k ∉ S, ∀ t : ℝ, actionRotation v k t ∈ K := by
    intro v hv k hk t j hj
    have hne : j ≠ -k := by change ¬0 < k at hk; omega
    rw [hrot]
    rw [(actionRotation_apply_ne _ (-k) j hne (-t)).1,(actionRotation_apply_ne _ (-k) j hne (-t)).2]
    exact hv j hj
  have hzK : z ∈ K := by
    intro k _hk
    rw [hz]
    exact ⟨rfl,rfl⟩
  have hwK := mem_of_isClosed_rotation_invariant_avoiding_set hp S K hK hKrot z hzK w ha hpos
  have h := hwK n hn
  rwa [hw] at h

end NLS.RealCoeff
