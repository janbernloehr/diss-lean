import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted

/-! # Actual symmetric finite-support approximations in raw real weighted norms -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS

/-- Symmetric raw truncation preserves physical reality and the central zero. -/
def physicalRealMeanZeroWeightedTruncate (w : Weight) (N : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule w) : physicalRealMeanZeroWeightedSubmodule w :=
  ⟨WeightedCoeff.truncate w 2 (Finset.Icc (-(N : ℤ)) N) q.val,by
    constructor
    · intro j
      have hn : -j∈Finset.Icc (-(N : ℤ)) N ↔ j∈Finset.Icc (-(N : ℤ)) N := by
        simp only [Finset.mem_Icc]
        omega
      change (WeightedCoeff.truncate w 2 _ q.val).val (-j)=conj ((WeightedCoeff.truncate w 2 _ q.val).val j)
      rw [WeightedCoeff.truncate_apply,WeightedCoeff.truncate_apply]
      by_cases hj : j∈Finset.Icc (-(N : ℤ)) N
      · rw [if_pos hj,if_pos (hn.mpr hj),q.property.1]
      · rw [if_neg hj,if_neg (fun h => hj (hn.mp h)),map_zero]
    · change (WeightedCoeff.truncate w 2 _ q.val).val 0=0
      rw [WeightedCoeff.truncate_apply]
      split_ifs
      · exact q.property.2
      · rfl⟩

@[simp] theorem physicalRealMeanZeroWeightedTruncate_coefficient (w : Weight) (N : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule w) (j : ℤ) :
    (physicalRealMeanZeroWeightedTruncate w N q).val.val j=
      if j∈Finset.Icc (-(N : ℤ)) N then q.val.val j else 0 :=
  WeightedCoeff.truncate_apply w 2 _ q.val j

/-- Actual positive raw Fourier modes vanish beyond the finite cutoff. -/
theorem physicalRealMeanZeroWeightedTruncate_positive_tail (w : Weight) (N : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule w) (j : ℕ+) (hj : N<(j : ℕ)) :
    (physicalRealMeanZeroWeightedTruncate w N q).val.val (j : ℤ)=0 := by
  rw [physicalRealMeanZeroWeightedTruncate_coefficient,if_neg]
  simp only [Finset.mem_Icc]
  omega

/-- The complete real mean-zero sequence converges in the ORIGINAL weighted Hilbert norm. -/
theorem tendsto_physicalRealMeanZeroWeightedTruncate (w : Weight)
    (q : physicalRealMeanZeroWeightedSubmodule w) :
    Tendsto (fun N => physicalRealMeanZeroWeightedTruncate w N q) atTop (𝓝 q) := by
  apply tendsto_subtype_rng.mpr
  exact (WeightedCoeff.tendsto_truncate w 2 (by simp) q.val).comp Finset.tendsto_Icc_neg

end NLS
