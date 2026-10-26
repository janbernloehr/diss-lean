import NLS.ZakharovShabat.L2WholeLineMatrixMultiplication

/-! # Norm estimates for the original physical Green-kernel action -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Matrix Complex
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- Entrywise matrix norm gives the dimension-two bound in the original pair norm. -/
theorem norm_wholeLineMatrixAction_le (M : Matrix (Fin 2) (Fin 2) ℂ) (v : ℂ × ℂ) :
    ‖wholeLineMatrixAction M v‖ ≤ 2*‖M‖*‖v‖ := by
  have hb (i : Fin 2) : ‖M i 0*v.1+M i 1*v.2‖ ≤ 2*‖M‖*‖v‖ := by
    calc
      ‖M i 0*v.1+M i 1*v.2‖ ≤ ‖M i 0*v.1‖+‖M i 1*v.2‖ := norm_add_le _ _
      _ = ‖M i 0‖*‖v.1‖+‖M i 1‖*‖v.2‖ := by rw [norm_mul,norm_mul]
      _ ≤ ‖M‖*‖v‖+‖M‖*‖v‖ := add_le_add
        (mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm M) (le_max_left _ _)
          (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm M) (le_max_right _ _)
          (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  exact max_le (hb 0) (hb 1)

/-- The signed physical pencil forcing preserves the original pair norm. -/
theorem norm_wholeLinePencilForcing_pair (v : ℂ × ℂ) :
    ‖(I*v.1,-I*v.2)‖ = ‖v‖ := by
  simp [Prod.norm_def]

/-- A uniform matrix bound controls the interval integral by the L1 mass of its input. -/
theorem norm_integral_wholeLineMatrixAction_le
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (v : ℝ → ℂ × ℂ)
    (a b C : ℝ) (hab : a ≤ b)
    (hv : IntervalIntegrable (fun s => ‖v s‖) volume a b)
    (hM : ∀ s ∈ Icc a b, ‖M s‖ ≤ C) :
    ‖∫ s in a..b, wholeLineMatrixAction (M s) (v s)‖ ≤
      2*C*(∫ s in a..b, ‖v s‖) := by
  calc
    _ ≤ ∫ s in a..b, (2*C)*‖v s‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hab _ (hv.const_mul (2*C))
      exact Filter.Eventually.of_forall (fun s hs =>
        (norm_wholeLineMatrixAction_le (M s) (v s)).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hM s ⟨hs.1.le,hs.2⟩) (by norm_num)) (norm_nonneg _)))
    _ = _ := intervalIntegral.integral_const_mul _ _

end NLS.ZakharovShabat
