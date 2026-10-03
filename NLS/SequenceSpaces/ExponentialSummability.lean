import NLS.SequenceSpaces.BoundedScalarProducts
import Mathlib.Analysis.Complex.Exponential

/-! # Exponentials of summable scalar sequences -/

noncomputable section
open scoped ENNReal
namespace NLS

/-- A scalar sequence summably close to one is bounded. -/
theorem exists_norm_bound_of_memlp_sub_one {p : ℝ≥0∞} {f : ℤ → ℂ}
    (hf : Memℓp (fun n => f n-1) p) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖f n‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_bound_of_memlp hf
  refine ⟨C+1,by linarith,fun n => ?_⟩
  calc
    ‖f n‖ = ‖(f n-1)+1‖ := by rw [sub_add_cancel]
    _ ≤ ‖f n-1‖+‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ C+1 := by simpa using add_le_add (hbound n) (le_refl ‖(1 : ℂ)‖)

/-- Exponentiation turns a summable scalar sequence into a summable deviation from one. -/
theorem memlp_exp_sub_one {p : ℝ≥0∞} {f : ℤ → ℂ} (hf : Memℓp f p) :
    Memℓp (fun n => Complex.exp (f n)-1) p := by
  obtain ⟨C,_,hC⟩ := exists_norm_bound_of_memlp hf
  apply (hf.norm.const_mul (Real.exp C)).mono
  intro n
  have h : ‖Complex.exp (f n)-1‖ ≤ ‖f n‖*Real.exp ‖f n‖ := by
    simpa using Complex.norm_exp_sub_sum_le_norm_mul_exp (f n) 1
  exact h.trans (by rw [mul_comm (Real.exp C)]; gcongr; exact hC n)

end NLS
