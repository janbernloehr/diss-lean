import NLS.SequenceSpaces.PositiveInsertion

/-! Zero extension of an arbitrary positive-index scalar series.
The literal values, absolute convergence and total sum are preserved. -/
noncomputable section
open Set
open scoped Classical
namespace NLS.LpSequence

def positiveScalarExtension (u : ℕ+ → ℂ) : ℤ → ℂ :=
  Function.extend positiveEmbedding u 0

theorem positiveScalarExtension_apply (u : ℕ+ → ℂ) (m : ℕ+) :
    positiveScalarExtension u ((m:ℕ):ℤ) = u m :=
  positiveEmbedding.injective.extend_apply u 0 m

theorem positiveScalarExtension_zero_of_not_mem_range (u : ℕ+ → ℂ) (k : ℤ)
    (hk : k ∉ range positiveEmbedding) : positiveScalarExtension u k = 0 :=
  Function.extend_apply' (f := positiveEmbedding) u (0:ℤ → ℂ) k hk

theorem summable_norm_positiveScalarExtension (u : ℕ+ → ℂ)
    (hu : Summable (fun m => ‖u m‖)) :
    Summable (fun k => ‖positiveScalarExtension u k‖) := by
  apply (positiveEmbedding.injective.summable_iff (fun k hk => ?_)).mp
  · change Summable (fun m : ℕ+ => ‖positiveScalarExtension u ((m:ℕ):ℤ)‖)
    simpa only [positiveScalarExtension_apply] using hu
  · simp only [positiveScalarExtension_zero_of_not_mem_range u k hk,norm_zero]

theorem tsum_positiveScalarExtension (u : ℕ+ → ℂ) :
    (∑' k : ℤ, positiveScalarExtension u k) = ∑' m : ℕ+, u m := by
  have he := positiveEmbedding.injective.tsum_eq (f := positiveScalarExtension u) (by
    intro k hk
    by_contra hn
    exact hk (positiveScalarExtension_zero_of_not_mem_range u k hn))
  change (∑' m : ℕ+, positiveScalarExtension u ((m:ℕ):ℤ)) = _ at he
  simpa only [positiveScalarExtension_apply] using he.symm

end NLS.LpSequence
