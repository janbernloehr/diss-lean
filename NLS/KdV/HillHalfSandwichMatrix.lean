import NLS.KdV.HillSandwichRows
import NLS.SequenceSpaces.Weighted

/-! Actual Fourier entries of the rough-potential half-denominator
sandwich, preserving the original coefficient difference l-m. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The literal normalized source perturbation matrix. -/
def hillHalfSandwichMatrix (r : ℝ) (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (z : ℂ) (l m : ℤ) : ℂ :=
  q.val (l-m)*hillHalfDenominatorRaw z l*hillHalfDenominatorRaw z m

/-- The raw potential coefficient is exactly its weighted l2 coefficient
multiplied by the positive source Sobolev weight. -/
theorem norm_sq_hillWeightedPotential_coefficient (r : ℝ)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (k : ℤ) :
    ‖q.val k‖^2 = ‖WeightedCoeff.weightEquiv (Weight.sobolev (-r)) 2 q k‖^2*
      (Weight.sobolev r k)^2 := by
  rw [WeightedCoeff.weightEquiv_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ((Weight.sobolev (-r)).positive k)]
  have hw : Weight.sobolev (-r) k*Weight.sobolev r k = 1 := by
    rw [Weight.sobolev_apply,Weight.sobolev_apply,← Real.rpow_add (by positivity),neg_add_cancel,Real.rpow_zero]
  calc
    _ = (Weight.sobolev (-r) k*Weight.sobolev r k)^2*‖q.val k‖^2 := by rw [hw];ring
    _ = _ := by ring

/-- The squared original matrix entry is exactly the weighted row kernel
times the squared original weighted potential coefficient. -/
theorem norm_sq_hillHalfSandwichMatrix_shift (r : ℝ)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (z : ℂ) (k m : ℤ) :
    ‖hillHalfSandwichMatrix r q z (m+k) m‖^2 =
      ‖WeightedCoeff.weightEquiv (Weight.sobolev (-r)) 2 q k‖^2 *
      ((Weight.sobolev r k)^2*‖z-(freeHillValue (m+k):ℂ)‖⁻¹*‖z-(freeHillValue m:ℂ)‖⁻¹) := by
  simp only [hillHalfSandwichMatrix,add_sub_cancel_left,norm_mul,mul_pow,norm_sq_hillHalfDenominatorRaw]
  rw [norm_sq_hillWeightedPotential_coefficient]
  ring

/-- Exact integer reindexing from matrix output/input to potential difference/input. -/
def hillMatrixFrequencyShear : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.2+p.1,p.2)
  invFun p := (p.1-p.2,p.2)
  left_inv := by intro p;ext <;> simp
  right_inv := by intro p;ext <;> simp

end NLS.KdV
