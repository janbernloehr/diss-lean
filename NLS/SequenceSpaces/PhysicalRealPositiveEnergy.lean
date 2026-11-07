import NLS.SequenceSpaces.PhysicalRealDeletedHilbert
import NLS.SequenceSpaces.HilbertCoordinateContinuity

/-! Exact positive-mode Hilbert energy on the physical real deleted space. -/
noncomputable section
open Complex
open scoped ENNReal ComplexConjugate
namespace NLS

theorem physicalRealDeleted_norm_sq_eq_twice_tsum_succ (a : physicalRealDeletedSubmodule) :
    ‖a‖^2=2*(∑' j : ℕ, ‖a.val.val ((j+1:ℕ):ℤ)‖^2) := by
  have hr := (periodOneL2Conjugation_fixed_iff _).mp
    ((deletedL2Conjugation_fixed_iff _).mp a.property)
  have hn : Summable (fun j : ℕ => ‖a.val.val (j:ℤ)‖^2) := by
    have h : Summable (fun k : ℤ => ‖a.val.val k‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        (lp.hasSum_norm (by norm_num : 0<(2:ℝ≥0∞).toReal) a.val.val).summable
    exact h.comp_injective (show Function.Injective (fun j : ℕ => (j:ℤ)) from Nat.cast_injective)
  have he := Coeff.norm_sq_eq_twice_tsum_nat a.val.val a.val.property
    (fun k => by rw [hr k,norm_conj])
  have hz : a.val.val 0=0 := a.val.property
  have hs := hn.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,Nat.cast_zero,hz,norm_zero,
    zero_pow (by decide : 2≠0),zero_add] at hs
  exact he.trans (congrArg (fun x : ℝ => 2*x) hs.symm)

theorem hasSum_physicalRealDeleted_positive_sq (a : physicalRealDeletedSubmodule) :
    HasSum (fun j : ℕ => ‖a.val.val ((j+1:ℕ):ℤ)‖^2) (‖a‖^2/2) := by
  have h : Summable (fun k : ℤ => ‖a.val.val k‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0<(2:ℝ≥0∞).toReal) a.val.val).summable
  have hs := (h.comp_injective (show Function.Injective (fun j : ℕ => (j:ℤ)) from
    Nat.cast_injective)).comp_injective (show Function.Injective (fun j : ℕ => j+1) from
      fun _ _ hj => Nat.add_right_cancel hj)
  have he : (∑' j : ℕ, ‖a.val.val ((j+1:ℕ):ℤ)‖^2)=‖a‖^2/2 := by
    linarith [physicalRealDeleted_norm_sq_eq_twice_tsum_succ a]
  exact he ▸ hs.hasSum

end NLS
