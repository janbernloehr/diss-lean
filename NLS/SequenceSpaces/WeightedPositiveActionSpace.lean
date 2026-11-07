import NLS.SequenceSpaces.WeightedPositiveActionModel
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! The ORIGINAL weighted positive-frequency action Banach model,
realized as a closed supported subspace, with an exact norm isometry. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.WeightedCoeff

def positiveSupportedSubmodule (w : Weight) : Submodule ℂ (WeightedCoeff w 1) where
  carrier := {a | ∀ j : ℤ, j≤0 → a.val j=0}
  zero_mem' := by intro j _;rfl
  add_mem' := by
    intro a b ha hb j hj
    change a.val j+b.val j=0
    rw [ha j hj,hb j hj,add_zero]
  smul_mem' := by
    intro c a ha j hj
    change c*a.val j=0
    rw [ha j hj,mul_zero]

theorem isClosed_positiveSupportedSubmodule (w : Weight) :
    IsClosed (positiveSupportedSubmodule w : Set (WeightedCoeff w 1)) := by
  have he : (positiveSupportedSubmodule w : Set (WeightedCoeff w 1))=
      ⋂ j : ℤ, ⋂ _ : j≤0, (evalCLM w 1 j) ⁻¹' {0} := by
    ext a
    simp only [mem_iInter,mem_preimage,mem_singleton_iff]
    rfl
  rw [he]
  exact isClosed_iInter (fun j => isClosed_iInter (fun _ => isClosed_singleton.preimage (evalCLM w 1 j).continuous))

instance (w : Weight) : CompleteSpace (positiveSupportedSubmodule w) :=
  (isClosed_positiveSupportedSubmodule w).completeSpace_coe

def positiveActionModelEquiv (w : Weight) (e : ℤ ≃ ℕ+) :
    Coeff 1 ≃ₗᵢ[ℂ] positiveSupportedSubmodule w where
  toFun b := ⟨positiveActionLift w e b,positiveActionLift_nonpositive w e b⟩
  invFun a := positiveActionRestriction w e a.val
  left_inv := positiveActionRestriction_lift w e
  right_inv a := Subtype.ext (positiveActionLift_restriction w e a.val a.property)
  map_add' a b := Subtype.ext ((positiveActionLift w e).map_add a b)
  map_smul' c a := Subtype.ext ((positiveActionLift w e).map_smul c a)
  norm_map' b := (positiveActionLift w e).norm_map b

theorem positiveActionModelEquiv_raw_index (w : Weight) (e : ℤ ≃ ℕ+) (b : Coeff 1) (k : ℤ) :
    ((positiveActionModelEquiv w e b).val).val (e k : ℤ)=b k/(w (e k : ℤ) : ℂ) :=
  positiveActionLift_index w e b k

theorem positiveActionModelEquiv_nonnegative (w : Weight) (e : ℤ ≃ ℕ+)
    (a : positiveSupportedSubmodule w) :
    a.val∈nonnegativeLocus w 1 ↔ (positiveActionModelEquiv w e).symm a∈Coeff.nonnegativeLocus 1 := by
  constructor
  · intro ha k
    change ((w (e k : ℤ) : ℂ)*a.val.val (e k : ℤ)).im=0 ∧
      0≤((w (e k : ℤ) : ℂ)*a.val.val (e k : ℤ)).re
    have h := (mem_nonnegativeLocus_iff w 1 a.val).mp ha (e k : ℤ)
    exact h
  · intro ha
    have h := (positiveActionLift_mem_positiveActionLocus w e _ ha).1
    rw [show positiveActionLift w e ((positiveActionModelEquiv w e).symm a)=a.val from
      positiveActionLift_restriction w e a.val a.property] at h
    exact h

end NLS.WeightedCoeff
