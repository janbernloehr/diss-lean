import NLS.SequenceSpaces.RealCoeff
import NLS.SequenceSpaces.PairNorm

/-! # Real Hilbert pairs constructed from summable squared coordinates -/
noncomputable section
open scoped ENNReal
namespace NLS

private theorem real_memℓp_two_of_summable_sq (x : ℤ → ℝ)
    (h : Summable (fun n => (x n)^2)) : Memℓp x 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using h

/-- A genuine pair of real ℓ² sequences, retaining the supplied coordinates. -/
def realHilbertPairFromSquares (x y : ℤ → ℝ)
    (h : Summable (fun n => (x n)^2+(y n)^2)) : WithLp 2 (RealCoeff 2 × RealCoeff 2) :=
  WithLp.toLp 2
    (⟨x,real_memℓp_two_of_summable_sq x (h.of_nonneg_of_le (fun n => sq_nonneg (x n))
      (fun n => le_add_of_nonneg_right (sq_nonneg (y n))))⟩,
     ⟨y,real_memℓp_two_of_summable_sq y (h.of_nonneg_of_le (fun n => sq_nonneg (y n))
      (fun n => le_add_of_nonneg_left (sq_nonneg (x n))))⟩)

@[simp] theorem realHilbertPairFromSquares_fst (x y : ℤ → ℝ)
    (h : Summable (fun n => (x n)^2+(y n)^2)) (n : ℤ) :
    (realHilbertPairFromSquares x y h).fst n = x n := rfl

@[simp] theorem realHilbertPairFromSquares_snd (x y : ℤ → ℝ)
    (h : Summable (fun n => (x n)^2+(y n)^2)) (n : ℤ) :
    (realHilbertPairFromSquares x y h).snd n = y n := rfl

/-- The pair uses the sum-of-squares norm, exactly as in the real model space. -/
theorem realHilbertPairFromSquares_norm_sq (x y : ℤ → ℝ)
    (h : Summable (fun n => (x n)^2+(y n)^2)) :
    ‖realHilbertPairFromSquares x y h‖^2 = ∑' n : ℤ, ((x n)^2+(y n)^2) := by
  have hx := h.of_nonneg_of_le (fun n => sq_nonneg (x n))
    (fun n => le_add_of_nonneg_right (sq_nonneg (y n)))
  have hy := h.of_nonneg_of_le (fun n => sq_nonneg (y n))
    (fun n => le_add_of_nonneg_left (sq_nonneg (x n)))
  have hp (a : RealCoeff 2) : ‖a‖^2 = ∑' n : ℤ, (a n)^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) a
  rw [WithLp.prod_norm_sq_eq_of_L2,hp,hp]
  change (∑' n : ℤ, (x n)^2)+(∑' n : ℤ, (y n)^2) = _
  exact (hx.tsum_add hy).symm

end NLS
