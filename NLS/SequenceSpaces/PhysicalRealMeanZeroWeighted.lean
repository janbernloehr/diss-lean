import NLS.SequenceSpaces.PhysicalRealSobolevInclusion
import NLS.SequenceSpaces.DeletedSymmetricTruncation

/-! # Actual raw real mean-zero weighted Fourier spaces

The raw real source/target spaces retain their literal weighted Hilbert
norms. Explicit real linear ISOMETRIES identify their raw coefficients
with the already-used normalized physical real deleted Hilbert space.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS

/-- ACTUAL raw weighted sequences with physical Fourier reality and mean
zero, carrying the inherited ORIGINAL weighted Hilbert norm. -/
def physicalRealMeanZeroWeightedSubmodule (w : Weight) : Submodule ℝ (WeightedCoeff w 2) where
  carrier := {q | (∀ j : ℤ, q.val (-j)=conj (q.val j)) ∧ q.val 0=0}
  zero_mem' := by constructor <;> simp
  add_mem' := by
    intro a b ha hb
    constructor
    · intro j
      change a.val (-j)+b.val (-j)=conj (a.val j+b.val j)
      rw [map_add,ha.1 j,hb.1 j]
    · change a.val 0+b.val 0=0
      rw [ha.2,hb.2,add_zero]
  smul_mem' := by
    intro r a ha
    constructor
    · intro j
      change (r : ℂ)*a.val (-j)=conj ((r : ℂ)*a.val j)
      rw [map_mul,conj_ofReal,ha.1 j]
    · change (r : ℂ)*a.val 0=0
      rw [ha.2,mul_zero]

@[simp] theorem mem_physicalRealMeanZeroWeightedSubmodule (w : Weight) (q : WeightedCoeff w 2) :
    q∈physicalRealMeanZeroWeightedSubmodule w ↔
      (∀ j : ℤ, q.val (-j)=conj (q.val j)) ∧ q.val 0=0 := Iff.rfl

/-- The literal weighted lift and projection give a real linear ISOMETRY
onto the entire actual raw real mean-zero weighted Fourier space. -/
def physicalRealMeanZeroWeightedIsometry (w : Weight) (hw : ∀ j, w (-j)=w j) :
    physicalRealDeletedSubmodule ≃ₗᵢ[ℝ] physicalRealMeanZeroWeightedSubmodule w where
  toFun a := ⟨WeightedCoeff.meanZeroWeightedLiftCLM w a.val,
    (WeightedCoeff.meanZeroWeightedLift_real_iff w hw a.val).mpr a.property,
    WeightedCoeff.meanZeroWeightedLift_zero w a.val⟩
  invFun q := ⟨WeightedCoeff.meanZeroWeightedProjectionCLM w q.val,
    meanZeroWeightedProjection_real w hw q.val q.property.1⟩
  left_inv a := Subtype.ext (WeightedCoeff.meanZeroWeightedProjection_lift w a.val)
  right_inv q := Subtype.ext (WeightedCoeff.meanZeroWeightedLift_projection w q.val q.property.2)
  map_add' a b := by
    apply Subtype.ext
    exact (WeightedCoeff.meanZeroWeightedLiftCLM w).map_add a.val b.val
  map_smul' r a := by
    apply Subtype.ext
    exact ((WeightedCoeff.meanZeroWeightedLiftCLM w).restrictScalars ℝ).map_smul r a.val
  norm_map' a := WeightedCoeff.meanZeroWeightedLift_norm w a.val

@[simp] theorem physicalRealMeanZeroWeightedIsometry_apply (w : Weight) (hw : ∀ j, w (-j)=w j)
    (a : physicalRealDeletedSubmodule) :
    (physicalRealMeanZeroWeightedIsometry w hw a).val=WeightedCoeff.meanZeroWeightedLiftCLM w a.val := rfl

@[simp] theorem physicalRealMeanZeroWeightedIsometry_symm_apply (w : Weight) (hw : ∀ j, w (-j)=w j)
    (q : physicalRealMeanZeroWeightedSubmodule w) :
    ((physicalRealMeanZeroWeightedIsometry w hw).symm q).val=WeightedCoeff.meanZeroWeightedProjectionCLM w q.val := rfl

/-- The raw physical real mean-zero weighted space is complete in its
ORIGINAL norm, rather than only after a topological renorming. -/
theorem completeSpace_physicalRealMeanZeroWeighted (w : Weight) (hw : ∀ j, w (-j)=w j) :
    CompleteSpace (physicalRealMeanZeroWeightedSubmodule w) :=
  (physicalRealMeanZeroWeightedIsometry w hw).symm.toIsometryEquiv.completeSpace

end NLS
