import NLS.SequenceSpaces.PhysicalRealMeanZeroWeightedExponent
import Mathlib.Order.Filter.AtTopBot.Interval

/-! # Symmetric truncation in the original real mean-zero weighted norm -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal ComplexConjugate
namespace NLS
variable {p : ℝ≥0∞} [Fact (1≤p)]

def physicalRealMeanZeroWeightedTruncateExponent {w : Weight} (N : ℕ)
    (q : physicalRealMeanZeroWeightedExponent w p) : physicalRealMeanZeroWeightedExponent w p :=
  ⟨WeightedCoeff.truncate w p (Finset.Icc (-(N : ℤ)) N) q.val,by
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

@[simp] theorem physicalRealMeanZeroWeightedTruncateExponent_apply {w : Weight} (N : ℕ)
    (q : physicalRealMeanZeroWeightedExponent w p) (j : ℤ) :
    (physicalRealMeanZeroWeightedTruncateExponent N q).val.val j =
      if j ∈ Finset.Icc (-(N : ℤ)) N then q.val.val j else 0 :=
  WeightedCoeff.truncate_apply w p _ q.val j

theorem tendsto_physicalRealMeanZeroWeightedTruncateExponent {w : Weight}
    (hp : p≠⊤) (q : physicalRealMeanZeroWeightedExponent w p) :
    Tendsto (fun N => physicalRealMeanZeroWeightedTruncateExponent N q) atTop (𝓝 q) := by
  apply tendsto_subtype_rng.mpr
  exact (WeightedCoeff.tendsto_truncate w p hp q.val).comp Finset.tendsto_Icc_neg

theorem physicalRealMeanZeroWeightedTruncateExponent_finiteSupport {w : Weight} (N : ℕ)
    (q : physicalRealMeanZeroWeightedExponent w p) :
    (Function.support (physicalRealMeanZeroWeightedTruncateExponent N q).val.val).Finite := by
  apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) N)).subset
  intro j hj
  by_contra hjS
  have hjS' : j∉Finset.Icc (-(N : ℤ)) N := hjS
  exact hj (by rw [physicalRealMeanZeroWeightedTruncateExponent_apply,if_neg hjS'])

end NLS
