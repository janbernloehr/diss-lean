import NLS.SequenceSpaces.FiniteHeadTailBound

/-! Full norm control for Banach-valued series with a finite head and one
literal ell1 tail majorant. Both absolute convergence and the norm bound
are retained before any coordinate evaluation or sequence realization. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E]

theorem summable_norm_and_tsum_norm_le_of_head_tail
    (f : ℤ → E) (S : Finset ℤ) (H : ℤ → ℝ) (a : Coeff 1) (C : ℝ) (hC : 0≤C)
    (hhead : ∀ j∈S, ‖f j‖≤H j) (htail : ∀ j∉S, ‖f j‖≤C*‖a j‖) :
    Summable (fun j => ‖f j‖) ∧ (∑' j : ℤ, ‖f j‖)≤(∑ j∈S, H j)+C*‖a‖ := by
  classical
  let M := fun j => (if j∈S then H j else 0)+C*‖a j‖
  have hh : Summable (fun j : ℤ => if j∈S then H j else 0) :=
    summable_of_ne_finset_zero (s := S) (fun j hj => if_neg hj)
  have ha : Summable (fun j : ℤ => ‖a j‖) := (lp.memℓp a).norm.summable_of_one
  have hM : Summable M := hh.add (ha.mul_left C)
  have hb (j : ℤ) : ‖f j‖≤M j := by
    dsimp only [M]
    by_cases hj : j∈S
    · rw [if_pos hj]
      exact (hhead j hj).trans (le_add_of_nonneg_right (by positivity))
    · simpa only [if_neg hj,zero_add] using htail j hj
  have hs := hM.of_nonneg_of_le (fun j => norm_nonneg (f j)) hb
  refine ⟨hs,(hs.tsum_le_tsum hb hM).trans_eq ?_⟩
  rw [Summable.tsum_add hh (ha.mul_left C),tsum_mul_left]
  have hhnorm : (∑' j : ℤ, if j∈S then H j else 0)=∑ j∈S,H j := by
    calc
      _=∑ j∈S, (if j∈S then H j else 0) := tsum_eq_sum (fun j hj => if_neg hj)
      _=_ := Finset.sum_congr rfl (fun j hj => if_pos hj)
  have hanorm : (∑' j : ℤ, ‖a j‖)=‖a‖ := by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using
      (lp.norm_rpow_eq_tsum (by norm_num : 0<(1 : ENNReal).toReal) a).symm
  rw [hhnorm,hanorm]

end NLS.Coeff
