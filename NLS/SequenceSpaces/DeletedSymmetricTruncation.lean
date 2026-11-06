import NLS.SequenceSpaces.DeletedRealConjugation
import NLS.SequenceSpaces.MeanZeroWeightedCoordinates
import NLS.SequenceSpaces.WeightedSourceSignedCompletion
import Mathlib.Order.Filter.AtTopBot.Interval

/-! # Finite real truncations in the deleted Hilbert coordinates

Symmetric truncation preserves the deleted mode and physical conjugation,
converges in the native Hilbert norm, and commutes with every weighted lift.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS

def deletedSymmetricTruncate (N : ℕ) (b : DeletedCoeff 2 0) : DeletedCoeff 2 0 :=
  ⟨Coeff.truncate (Finset.Icc (-(N : ℤ)) N) b.val,by
    change Coeff.truncate _ b.val 0=0
    rw [Coeff.truncate_apply]
    split_ifs
    · exact b.property
    · rfl⟩

@[simp] theorem deletedSymmetricTruncate_apply (N : ℕ) (b : DeletedCoeff 2 0) (j : ℤ) :
    (deletedSymmetricTruncate N b).val j=
      if j∈Finset.Icc (-(N : ℤ)) N then b.val j else 0 := Coeff.truncate_apply _ _ _

theorem deletedSymmetricTruncate_finiteSupport (N : ℕ) (b : DeletedCoeff 2 0) :
    (Function.support (deletedSymmetricTruncate N b).val).Finite := by
  apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) N)).subset
  intro j hj
  by_contra hjN
  apply hj
  rw [deletedSymmetricTruncate_apply]
  split_ifs with h
  · exact (hjN h).elim
  · rfl

theorem deletedSymmetricTruncate_real (N : ℕ) (b : DeletedCoeff 2 0)
    (hb : deletedL2Conjugation b=b) :
    deletedL2Conjugation (deletedSymmetricTruncate N b)=deletedSymmetricTruncate N b := by
  have hr := (periodOneL2Conjugation_fixed_iff b.val).mp ((deletedL2Conjugation_fixed_iff b).mp hb)
  apply (deletedL2Conjugation_fixed_iff _).mpr
  apply (periodOneL2Conjugation_fixed_iff _).mpr
  intro j
  have hneg : -j∈Finset.Icc (-(N : ℤ)) N ↔ j∈Finset.Icc (-(N : ℤ)) N := by
    simp only [Finset.mem_Icc]
    omega
  by_cases hj : j∈Finset.Icc (-(N : ℤ)) N
  · simp only [deletedSymmetricTruncate_apply,if_pos hj,if_pos (hneg.mpr hj),hr j]
  · simp only [deletedSymmetricTruncate_apply,if_neg hj,if_neg (fun h => hj (hneg.mp h)),map_zero]

theorem tendsto_deletedSymmetricTruncate (b : DeletedCoeff 2 0) :
    Tendsto (fun N => deletedSymmetricTruncate N b) atTop (𝓝 b) := by
  apply tendsto_subtype_rng.mpr
  exact (Coeff.tendsto_truncate (by norm_num : (2 : ℝ≥0∞)≠⊤) b.val).comp Finset.tendsto_Icc_neg

theorem meanZeroWeightedLift_deletedSymmetricTruncate (w : Weight) (N : ℕ) (b : DeletedCoeff 2 0) :
    WeightedCoeff.meanZeroWeightedLiftCLM w (deletedSymmetricTruncate N b)=
      WeightedCoeff.truncate w 2 (Finset.Icc (-(N : ℤ)) N)
        (WeightedCoeff.meanZeroWeightedLiftCLM w b) := by
  apply Subtype.ext
  funext j
  rw [WeightedCoeff.truncate_apply]
  change (deletedSymmetricTruncate N b).val j/(w j : ℂ)=
    if j∈Finset.Icc (-(N : ℤ)) N then b.val j/(w j : ℂ) else 0
  rw [deletedSymmetricTruncate_apply]
  split_ifs <;> simp only [zero_div]

theorem meanZeroWeightedProjection_real (w : Weight) (hw : ∀ j, w (-j)=w j)
    (a : WeightedCoeff w 2) (ha : ∀ j, a.val (-j)=conj (a.val j)) :
    deletedL2Conjugation (WeightedCoeff.meanZeroWeightedProjectionCLM w a)=
      WeightedCoeff.meanZeroWeightedProjectionCLM w a := by
  change deletedL2Conjugation (Coeff.deleteCoordinateTo 0 (WeightedCoeff.weightIsometry w 2 a))=
    Coeff.deleteCoordinateTo 0 (WeightedCoeff.weightIsometry w 2 a)
  rw [←deleteCoordinateTo_conjugation,
    (WeightedCoeff.weightIsometry_fixed_iff_raw w hw a).mpr ha]

theorem meanZeroWeightedLift_real (w : Weight) (hw : ∀ j, w (-j)=w j)
    (b : DeletedCoeff 2 0) (hb : deletedL2Conjugation b=b) :
    (WeightedCoeff.meanZeroWeightedLiftCLM w b).val 0=0 ∧
      ∀ j, (WeightedCoeff.meanZeroWeightedLiftCLM w b).val (-j)=
        conj ((WeightedCoeff.meanZeroWeightedLiftCLM w b).val j) := by
  constructor
  · change b.val 0/(w 0 : ℂ)=0
    have h0 : b.val 0=0 := b.property
    rw [h0,zero_div]
  · apply (WeightedCoeff.weightIsometry_fixed_iff_raw w hw _).mp
    change periodOneL2Conjugation (WeightedCoeff.weightIsometry w 2
        ((WeightedCoeff.weightIsometry w 2).symm b.val))=
      WeightedCoeff.weightIsometry w 2 ((WeightedCoeff.weightIsometry w 2).symm b.val)
    simpa only [LinearIsometryEquiv.apply_symm_apply] using (deletedL2Conjugation_fixed_iff b).mp hb

end NLS
