import NLS.Articles.KdVConvexity.ActionEmbedding
import NLS.SequenceSpaces.HilbertReindexIsometry

/-! # The inverse of the literal positive-index Hilbert action reindexing -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

def actionUnreindex : Coeff 2 →ₗᵢ[ℂ] ActionSpace :=
  NLS.SequenceSpaces.hilbertReindexIsometry actionIndexEquiv

@[simp] theorem actionUnreindex_apply (b : Coeff 2) (n : ℕ+) :
    actionUnreindex b n = b (actionIndexEquiv.symm n) := rfl

@[simp] theorem actionReindex_actionUnreindex (b : Coeff 2) : actionReindex (actionUnreindex b) = b := by
  ext k
  simp only [actionReindex_apply,actionUnreindex_apply,Equiv.symm_apply_apply]

@[simp] theorem actionUnreindex_actionReindex (a : ActionSpace) : actionUnreindex (actionReindex a) = a := by
  ext n
  simp only [actionUnreindex_apply,actionReindex_apply,Equiv.apply_symm_apply]

theorem actionIndexEquiv_nat_index (n : ℕ+) : Equiv.intEquivNat (actionIndexEquiv.symm n)+1 = (n : ℕ) := by
  have he := congrArg (fun m : ℕ+ => (m : ℕ)) (actionIndexEquiv.apply_symm_apply n)
  change (Equiv.intEquivNat (actionIndexEquiv.symm n)).succ = (n : ℕ) at he
  simpa only [Nat.succ_eq_add_one] using he

end NLS.Articles.KdVConvexity
