import NLS.MKdV.MiuraCartesianPhaseSaturation
import NLS.MKdV.MiuraL2CentralActionZero
import NLS.ZakharovShabat.SourceDiagonalCoordinateAmbiguity

/-! # Faithfulness of positive NLS coordinates on physical Cartesian fibers -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraRealDiagonalL2Source (a : MiuraRealL2) : realTypeSourceSubmodule 2 :=
  ⟨scalarL2Diagonal a.val,(scalarL2Diagonal_realDiagonal a.val a.property).1⟩

theorem miuraNLS_action_re_eq_of_sequence_eq (a b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val) (n : ℤ) :
    (sourceRealAction (by simp) (by norm_num) (miuraRealDiagonalL2Source a).val
      (miuraRealDiagonalL2Source a).property n).re =
    (sourceRealAction (by simp) (by norm_num) (miuraRealDiagonalL2Source b).val
      (miuraRealDiagonalL2Source b).property n).re := by
  have h := congrArg (fun z : Coeff 1 => (z n).re) hI
  rw [miuraOriginalNLSActionSequence_apply _ (real_mem_miuraOriginalNLSActionDomain _ a.property),
    miuraOriginalNLSActionSequence_apply _ (real_mem_miuraOriginalNLSActionDomain _ b.property)] at h
  change (sourceComplexAction (by simp) (by norm_num) n (miuraRealDiagonalL2Source a).val).re =
    (sourceComplexAction (by simp) (by norm_num) n (miuraRealDiagonalL2Source b).val).re at h
  rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n
      (miuraRealDiagonalL2Source a).val (miuraRealDiagonalL2Source a).property,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n
      (miuraRealDiagonalL2Source b).val (miuraRealDiagonalL2Source b).property] at h
  exact h

/-- On an original NLS action fiber, equality of the actual physical
Cartesian map fixes all positive original NLS coordinate pairs. -/
theorem positive_NLS_coordinates_eq_of_miuraCartesian_eq (a b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val)
    (hM : miuraPositiveCartesianMap a.val = miuraPositiveCartesianMap b.val)
    (n : ℤ) (hn : 0 < n) :
    (miuraActionFlowFamily.data.hilbertRealHomeomorph (miuraRealDiagonalL2Source a)).1 n =
      (miuraActionFlowFamily.data.hilbertRealHomeomorph (miuraRealDiagonalL2Source b)).1 n ∧
    (miuraActionFlowFamily.data.hilbertRealHomeomorph (miuraRealDiagonalL2Source a)).2 n =
      (miuraActionFlowFamily.data.hilbertRealHomeomorph (miuraRealDiagonalL2Source b)).2 n := by
  let φ : realDiagonalSourceLocus 2 := ⟨scalarL2Diagonal a.val,scalarL2Diagonal_realDiagonal a.val a.property⟩
  let ψ : realDiagonalSourceLocus 2 := ⟨scalarL2Diagonal b.val,scalarL2Diagonal_realDiagonal b.val b.property⟩
  have hiso : miuraRealDiagonalL2Source b ∈ sourceIsospectralSet (by simp) (miuraRealDiagonalL2Source a) := by
    rw [sourceIsospectralSet_eq_actionLevelSet_all_exponents (by simp) (by norm_num)]
    exact fun k => (miuraNLS_action_re_eq_of_sequence_eq a b hI k).symm
  have hr := sourceDiagonalActionRoot_eq_of_isospectral (by simp) (by norm_num) φ ψ hiso n (ne_of_gt hn)
  have hpos := (sourceDiagonalActionRoot_real_positive (by simp) (by norm_num) φ n hn).2
  have hr0 : sourceDiagonalActionRoot (by simp) (by norm_num) n φ.val ≠ 0 := by
    intro he; rw [he] at hpos; exact (lt_irrefl 0 hpos)
  have hnN : 1 ≤ n.toNat := by omega
  have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
  have hC := congrArg (miuraPositiveCartesianEval (n.toNat : ℤ)) hM
  rw [miuraPositiveCartesianMap_positive a.val a.property n.toNat hnN,
    miuraPositiveCartesianMap_positive b.val b.property n.toNat hnN] at hC
  simp only [miuraL2CartesianCoordinates,hi] at hC
  change sourceDiagonalActionRoot (by simp) (by norm_num) n (scalarL2Diagonal b.val) =
    sourceDiagonalActionRoot (by simp) (by norm_num) n (scalarL2Diagonal a.val) at hr
  rw [hr] at hC
  have hx := mul_left_cancel₀ hr0 (congrArg Prod.fst hC)
  have hy := mul_left_cancel₀ hr0 (neg_injective (congrArg Prod.snd hC))
  exact ⟨congrArg Complex.re hx,congrArg Complex.re hy⟩

/-- The only possible ambiguity on a joint original-NLS-action Cartesian
fiber is the actual central NLS half-turn. -/
theorem miuraCartesian_jointFiber_eq_or_central_halfTurn (a b : MiuraRealL2)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val)
    (hM : miuraPositiveCartesianMap a.val = miuraPositiveCartesianMap b.val) :
    miuraRealDiagonalL2Source b = miuraRealDiagonalL2Source a ∨
      miuraRealDiagonalL2Source b = miuraActionFlowFamily.data.hilbertActionRotation
        (miuraRealDiagonalL2Source a) 0 Real.pi := by
  exact miuraActionFlowFamily.data.diagonal_eq_or_central_halfTurn _ _
    (by exact (scalarL2Diagonal_fst a.val).trans (scalarL2Diagonal_snd a.val).symm)
    (by exact (scalarL2Diagonal_fst b.val).trans (scalarL2Diagonal_snd b.val).symm)
    (miuraNLS_action_re_eq_of_sequence_eq a b hI)
    (positive_NLS_coordinates_eq_of_miuraCartesian_eq a b hI hM)

/-- Zero mean removes the central ambiguity. This is a global uniqueness
statement within the actual original NLS action fiber. -/
theorem miuraCartesian_jointFiber_injective_of_mean_zero (a b : MiuraRealL2) (hm : a.val 0 = 0)
    (hI : miuraOriginalNLSActionSequence a.val = miuraOriginalNLSActionSequence b.val)
    (hM : miuraPositiveCartesianMap a.val = miuraPositiveCartesianMap b.val) : b = a := by
  have h0 : (sourceRealAction (by simp) (by norm_num) (miuraRealDiagonalL2Source a).val
      (miuraRealDiagonalL2Source a).property 0).re = 0 := by
    have h := miuraOriginalNLSActionSequence_zero_of_mean_zero a.val a.property hm
    rw [miuraOriginalNLSActionSequence_apply _ (real_mem_miuraOriginalNLSActionDomain _ a.property)] at h
    change sourceComplexAction (by simp) (by norm_num) 0 (miuraRealDiagonalL2Source a).val = 0 at h
    rw [sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) 0
        (miuraRealDiagonalL2Source a).val (miuraRealDiagonalL2Source a).property] at h
    simp only [h,Complex.zero_re]
  have he := miuraActionFlowFamily.data.diagonal_eq_of_positive_coordinates_of_central_action_zero
    (miuraRealDiagonalL2Source a) (miuraRealDiagonalL2Source b)
    ((scalarL2Diagonal_fst a.val).trans (scalarL2Diagonal_snd a.val).symm)
    ((scalarL2Diagonal_fst b.val).trans (scalarL2Diagonal_snd b.val).symm)
    (miuraNLS_action_re_eq_of_sequence_eq a b hI)
    (positive_NLS_coordinates_eq_of_miuraCartesian_eq a b hI hM) h0
  apply Subtype.ext
  have h := congrArg (fun φ : realTypeSourceSubmodule 2 => φ.val.fst) he
  change (scalarL2Diagonal b.val).fst = (scalarL2Diagonal a.val).fst at h
  simpa only [scalarL2Diagonal_fst] using h

end NLS.MKdV
