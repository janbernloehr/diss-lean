import NLS.SequenceSpaces.LinearWeightLattice

/-! # A reciprocal-square budget uniform in the omitted integer index -/
noncomputable section
namespace NLS.ReciprocalSeries

/-- Every finite translated reciprocal-square sum is bounded by 7/2.
The resonant term is zero under Lean's division convention. -/
theorem sum_shifted_reciprocal_sq_le (s : Finset ℤ) (n : ℤ) :
    (∑ m ∈ s, (1/|((m-n:ℤ):ℝ)|)^2) ≤ (7/2:ℝ) := by
  have hs : Summable (fun m : ℤ => puncturedInverseSq (m-n)) :=
    summable_puncturedInverseSq.comp_injective (Equiv.subRight n).injective
  have h := hs.sum_le_tsum s (fun m _ => puncturedInverseSq_nonneg (m-n))
  have he : (∑' m : ℤ, puncturedInverseSq (m-n)) = ∑' m : ℤ, puncturedInverseSq m := by
    simpa only [Equiv.subRight_apply] using (Equiv.subRight n).tsum_eq puncturedInverseSq
  rw [he] at h
  simpa only [puncturedInverseSq,div_pow,one_pow] using h.trans tsum_puncturedInverseSq_le

end NLS.ReciprocalSeries
