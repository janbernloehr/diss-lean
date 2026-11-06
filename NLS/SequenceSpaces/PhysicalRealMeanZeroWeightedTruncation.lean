import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted

/-! # Symmetric truncation in the original real mean-zero weighted norm -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ComplexConjugate
namespace NLS

def physicalRealMeanZeroWeightedTruncate {w : Weight} (N : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule w) : physicalRealMeanZeroWeightedSubmodule w :=
  ⟨WeightedCoeff.truncate w 2 (Finset.Icc (-(N : ℤ)) N) q.val,by
    constructor
    · intro j
      have hn : -j ∈ Finset.Icc (-(N : ℤ)) N ↔ j ∈ Finset.Icc (-(N : ℤ)) N := by
        simp only [Finset.mem_Icc]
        omega
      simp only [WeightedCoeff.truncate_apply,hn]
      split_ifs
      · exact q.property.1 j
      · exact (map_zero _).symm
    · rw [WeightedCoeff.truncate_apply]
      split_ifs
      · exact q.property.2
      · rfl⟩

@[simp] theorem physicalRealMeanZeroWeightedTruncate_apply {w : Weight} (N : ℕ)
    (q : physicalRealMeanZeroWeightedSubmodule w) (j : ℤ) :
    (physicalRealMeanZeroWeightedTruncate N q).val.val j =
      if j ∈ Finset.Icc (-(N : ℤ)) N then q.val.val j else 0 :=
  WeightedCoeff.truncate_apply w 2 _ q.val j

theorem tendsto_physicalRealMeanZeroWeightedTruncate {w : Weight}
    (q : physicalRealMeanZeroWeightedSubmodule w) :
    Tendsto (fun N => physicalRealMeanZeroWeightedTruncate N q) atTop (𝓝 q) := by
  apply tendsto_subtype_rng.mpr
  exact (WeightedCoeff.tendsto_truncate w 2 (by norm_num) q.val).comp Finset.tendsto_Icc_neg

end NLS
