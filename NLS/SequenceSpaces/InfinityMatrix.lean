import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Bounded operators on infinity coefficients from a common summable row majorant -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

/-- Every row acts absolutely on every bounded coefficient sequence. -/
theorem summable_norm_matrixRow (M : ℤ → ℤ → ℂ) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0≤g k) (hM : ∀ m k, ‖M m k‖≤g k)
    (x : Coeff ⊤) (m : ℤ) : Summable (fun k => ‖M m k*x k‖) := by
  apply (hg.mul_right ‖x‖).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  rw [norm_mul]
  exact mul_le_mul (hM m k) (lp.norm_apply_le_norm (by simp) x k) (norm_nonneg _) (hg0 k)

/-- Absolute row sums have the common l1-kernel times linfinity-input bound. -/
theorem norm_matrixRow_tsum_le (M : ℤ → ℤ → ℂ) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0≤g k) (hM : ∀ m k, ‖M m k‖≤g k)
    (x : Coeff ⊤) (m : ℤ) :
    ‖∑' k, M m k*x k‖ ≤ (∑' k, g k)*‖x‖ := by
  apply (norm_tsum_le_tsum_norm (summable_norm_matrixRow M g hg hg0 hM x m)).trans
  rw [← tsum_mul_right]
  apply (summable_norm_matrixRow M g hg hg0 hM x m).tsum_le_tsum _ (hg.mul_right ‖x‖)
  intro k
  rw [norm_mul]
  exact mul_le_mul (hM m k) (lp.norm_apply_le_norm (by simp) x k) (norm_nonneg _) (hg0 k)

/-- The actual summed sequence, rather than a formal matrix expression. -/
def infinityMatrixSum (M : ℤ → ℤ → ℂ) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0≤g k) (hM : ∀ m k, ‖M m k‖≤g k)
    (x : Coeff ⊤) : Coeff ⊤ :=
  ⟨fun m => ∑' k, M m k*x k, memℓp_infty ⟨(∑' k,g k)*‖x‖, by
    rintro _ ⟨m,rfl⟩
    exact norm_matrixRow_tsum_le M g hg hg0 hM x m⟩⟩

/-- Uniformly summable rows define an actual continuous linear endpoint operator. -/
def infinityMatrixCLM (M : ℤ → ℤ → ℂ) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0≤g k) (hM : ∀ m k, ‖M m k‖≤g k) :
    Coeff ⊤ →L[ℂ] Coeff ⊤ :=
  LinearMap.mkContinuous
    { toFun := infinityMatrixSum M g hg hg0 hM
      map_add' x y := by
        ext m
        change (∑' k, M m k*(x k+y k)) = (∑' k, M m k*x k)+(∑' k, M m k*y k)
        simp only [mul_add]
        exact ((summable_norm_matrixRow M g hg hg0 hM x m).of_norm).tsum_add
          ((summable_norm_matrixRow M g hg hg0 hM y m).of_norm)
      map_smul' c x := by
        ext m
        change (∑' k, M m k*(c*x k)) = c*(∑' k, M m k*x k)
        simp only [mul_left_comm (M m _) c]
        exact tsum_mul_left }
    (∑' k,g k) (by
      intro x
      apply lp.norm_le_of_forall_le
        (mul_nonneg (tsum_nonneg hg0) (norm_nonneg x))
      exact norm_matrixRow_tsum_le M g hg hg0 hM x)

@[simp] theorem infinityMatrixCLM_apply (M : ℤ → ℤ → ℂ) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0≤g k) (hM : ∀ m k, ‖M m k‖≤g k)
    (x : Coeff ⊤) (m : ℤ) :
    infinityMatrixCLM M g hg hg0 hM x m = ∑' k, M m k*x k := rfl

theorem norm_infinityMatrixCLM_apply_le (M : ℤ → ℤ → ℂ) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0≤g k) (hM : ∀ m k, ‖M m k‖≤g k)
    (x : Coeff ⊤) : ‖infinityMatrixCLM M g hg hg0 hM x‖ ≤ (∑' k,g k)*‖x‖ := by
  apply lp.norm_le_of_forall_le (mul_nonneg (tsum_nonneg hg0) (norm_nonneg x))
  exact norm_matrixRow_tsum_le M g hg hg0 hM x

end NLS.Coeff
