import NLS.SequenceSpaces.DeletedSymmetricTruncation
import NLS.SequenceSpaces.MeanZeroWeightedReality

/-! # Every weighted target contains the verified finite real approximants

The existing actual symmetric deleted-coordinate truncation, its real
form preservation and native norm convergence are reused unchanged.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

/-- Every finite actual approximant belongs to EVERY native weighted
target after literal mean-zero lifting. No topological norm is replaced. -/
theorem deletedSymmetricTruncate_weighted_mem (S : ℕ) (a : DeletedCoeff 2 0) (v w : Weight) :
    Memℓp (fun j => (w j : ℂ)*(WeightedCoeff.meanZeroWeightedLiftCLM v
      (deletedSymmetricTruncate S a)).val j) 2 := by
  let f := fun j => (w j : ℂ)*(WeightedCoeff.meanZeroWeightedLiftCLM v (deletedSymmetricTruncate S a)).val j
  have hf (j : ℤ) (hj : f j ≠ 0) : j ∈ Finset.Icc (-(S : ℤ)) S := by
    by_contra hnot
    apply hj
    dsimp only [f]
    rw [WeightedCoeff.meanZeroWeightedLift_apply,deletedSymmetricTruncate_apply,if_neg hnot,zero_div,mul_zero]
  let c : Coeff 2 := Coeff.ofFinsupp (Finsupp.onFinset (Finset.Icc (-(S : ℤ)) S) f hf)
  have he : (fun j => c j) = f := by
    funext j
    exact Coeff.ofFinsupp_apply _ j
  change Memℓp f 2
  exact he ▸ lp.memℓp c

end NLS
