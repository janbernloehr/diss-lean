import NLS.SequenceSpaces.Truncation

/-!
# Bounded Fourier multipliers

A bounded complex symbol acts continuously on every Banach coefficient space,
including `p = ∞`. This is the basic interface for subsequent free-resolvent
constructions; no resolvent or spectral assertions are assumed here.
-/

open scoped ENNReal
noncomputable section

namespace NLS
namespace Coeff

variable {p : ℝ≥0∞}

/-- Pointwise multiplication by a bounded Fourier symbol. -/
def multiplier (m : Coeff ⊤) (a : Coeff p) : Coeff p :=
  ⟨fun n => m n * a n, by
    apply ((lp.memℓp a).norm.const_mul ‖m‖).mono
    intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (lp.norm_apply_le_norm (by simp) m n) (norm_nonneg _)⟩

@[simp]
theorem multiplier_apply (m : Coeff ⊤) (a : Coeff p) (n : ℤ) :
    multiplier m a n = m n * a n := rfl

@[simp]
theorem multiplier_add (m : Coeff ⊤) (a b : Coeff p) :
    multiplier m (a + b) = multiplier m a + multiplier m b := by
  ext n
  exact mul_add _ _ _

@[simp]
theorem multiplier_smul (m : Coeff ⊤) (c : ℂ) (a : Coeff p) :
    multiplier m (c • a) = c • multiplier m a := by
  ext n
  exact mul_left_comm _ _ _

/-- The multiplier norm is bounded by the supremum norm of its symbol. -/
theorem norm_multiplier_le [Fact (1 ≤ p)] (m : Coeff ⊤) (a : Coeff p) :
    ‖multiplier m a‖ ≤ ‖m‖ * ‖a‖ := by
  have h : ‖multiplier m a‖ ≤ ‖(‖m‖ : ℂ) • a‖ := by
    apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
    intro n
    simp only [multiplier_apply, norm_mul, lp.coeFn_smul, Pi.smul_apply,
      norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg m)]
    exact mul_le_mul_of_nonneg_right
      (lp.norm_apply_le_norm (by simp) m n) (norm_nonneg _)
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg m)] using h

/-- Bounded Fourier multipliers as continuous linear operators. -/
def multiplierCLM [Fact (1 ≤ p)] (m : Coeff ⊤) : Coeff p →L[ℂ] Coeff p :=
  LinearMap.mkContinuous
    { toFun := multiplier m
      map_add' := multiplier_add m
      map_smul' := multiplier_smul m }
    ‖m‖ (norm_multiplier_le m)

@[simp]
theorem multiplierCLM_apply [Fact (1 ≤ p)] (m : Coeff ⊤) (a : Coeff p) :
    multiplierCLM m a = multiplier m a := rfl

/-- Diagonal multipliers commute with every finite Fourier projection. -/
theorem multiplier_truncate (m : Coeff ⊤) (s : Finset ℤ) (a : Coeff p) :
    multiplier m (truncate s a) = truncate s (multiplier m a) := by
  ext n
  by_cases hn : n ∈ s <;> simp [hn]

end Coeff
end NLS
