import NLS.SequenceSpaces.LinearSpectralWeight

/-! # Corrected weight-growth bound from Section 23

The printed w(n) ≤ w(0)^|n| is false. The value at index one gives
an actual geometric majorant, hence at most exponential growth.
-/
noncomputable section
namespace NLS.SpectralWeight

/-- Every spectral weight has a geometric majorant with base w(1).
The factor w(0) includes the zero index, without assuming w(0)=1. -/
theorem le_geometric (w : SpectralWeight) (n : ℤ) :
    w n ≤ w 0 * (w 1)^n.natAbs := by
  have h (k : ℕ) : w (k : ℤ) ≤ w 0 * (w 1)^k := by
    induction k with
    | zero => simp
    | succ k hk =>
      calc
        w ((k+1 : ℕ) : ℤ) ≤ w (k : ℤ)*w 1 := by
          simpa only [Nat.cast_add,Nat.cast_one] using w.add_le (k : ℤ) 1
        _ ≤ (w 0*(w 1)^k)*w 1 := mul_le_mul_of_nonneg_right hk (w.positive 1).le
        _ = w 0*(w 1)^(k+1) := by rw [pow_succ,mul_assoc]
  simpa only [Int.natCast_natAbs,w.apply_abs] using h n.natAbs

/-- The printed base w(0) fails even for a normalized weight in M₁. -/
theorem section23_printed_geometric_bound_counterexample : ∃ w : SpectralWeight, w.HasLinearFactor ∧ ¬ w 1 ≤ (w 0)^(Int.natAbs (1:ℤ)) := by
  refine ⟨one.withLinearFactor,hasLinearFactor_withLinearFactor one,?_⟩
  norm_num [withLinearFactor_apply,one_apply]
end NLS.SpectralWeight
