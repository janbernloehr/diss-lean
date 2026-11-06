import NLS.SequenceSpaces.ClosedTailRotationSaturation

/-! # Continuous invariants on complete infinite action tori

Finite coordinate rotations determine every continuous observable on an
entire action fiber, in the actual sequence norm. Retained head coordinates
are fixed literally, so their signs are not lost by taking actions.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.RealCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {Y : Type*} [TopologicalSpace Y] [T1Space Y]

theorem eq_of_continuous_tail_rotation_invariant (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (RealCoeff p × RealCoeff p) → Y) (hf : Continuous f)
    (hrot : ∀ z k, k ∉ S → ∀ t : ℝ, f (actionRotation z k t) = f z)
    (z w : RealCoeff p × RealCoeff p)
    (ha : ∀ n, pairAction z n = pairAction w n)
    (hh : ∀ n ∈ S, z.1 n = w.1 n ∧ z.2 n = w.2 n) : f w = f z := by
  let K := f ⁻¹' {f z}
  have hK : IsClosed K := isClosed_singleton.preimage hf
  exact mem_of_isClosed_tail_rotation_invariant hp S K hK
    (fun v hv k hk t => by change f (actionRotation v k t) = f z; exact (hrot v k hk t).trans hv)
    z rfl w ha hh

end NLS.RealCoeff
