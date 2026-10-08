import NLS.ComplexAnalysis.SharpExponentialRemainder
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! # Signed-sum infinite-product estimates from Appendix D.1–D.3

Write A for the complex sum, S for the sum of norms, and B for the sum of
squared norms. The half-unit hypothesis bounds the logarithmic correction
by B. Comparing the product with exp A then retains cancellation in A.
-/
noncomputable section
namespace NLS.ComplexAnalysis
variable {ι : Type*} (u : ι → ℂ) (hu : Summable (fun i => ‖u i‖))
variable (hhalf : ∀ i, ‖u i‖ ≤ (1:ℝ)/2)
include hu hhalf

/-- Squared norms are summable under the source's half-unit assumption. -/
theorem summable_sq_norm_of_half_bound : Summable (fun i => ‖u i‖^2) := by
  apply hu.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_)
  have h := hhalf i
  nlinarith [norm_nonneg (u i)]

/-- The sum of squared norms is at most the square of their sum. -/
theorem tsum_sq_norm_le_sq_tsum_norm : (∑' i, ‖u i‖^2) ≤ (∑' i, ‖u i‖)^2 := by
  have hs (i : ι) : ‖u i‖ ≤ ∑' j, ‖u j‖ := hu.le_tsum i (fun _ _ => norm_nonneg _)
  calc
    _ ≤ ∑' i, ‖u i‖*(∑' j, ‖u j‖) :=
      (summable_sq_norm_of_half_bound u hu hhalf).tsum_le_tsum
        (fun i => by nlinarith [norm_nonneg (u i),hs i]) (hu.mul_right _)
    _ = _ := by rw [tsum_mul_right]; ring

omit hu hhalf in
/-- At radius one half, the logarithmic remainder is bounded by the square. -/
theorem norm_log_one_add_sub_le_sq {z : ℂ} (hz : ‖z‖ ≤ (1:ℝ)/2) :
    ‖Complex.log (1+z)-z‖ ≤ ‖z‖^2 := by
  have hlt : ‖z‖ < 1 := by linarith
  apply (Complex.norm_log_one_add_sub_self_le hlt).trans
  have hi : (1-‖z‖)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ (sub_pos.mpr hlt)).mpr
    linarith
  nlinarith [sq_nonneg ‖z‖]

/-- The total logarithmic correction is controlled by B, retaining the signed sum. -/
theorem norm_tsum_log_one_add_sub_tsum_le :
    ‖(∑' i, Complex.log (1+u i))-(∑' i, u i)‖ ≤ ∑' i, ‖u i‖^2 := by
  have hn : Summable (fun i => ‖Complex.log (1+u i)-u i‖) :=
    (summable_sq_norm_of_half_bound u hu hhalf).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => norm_log_one_add_sub_le_sq (hhalf i))
  rw [← (Complex.summable_log_one_add_of_summable hu.of_norm).tsum_sub hu.of_norm]
  exact (norm_tsum_le_tsum_norm hn).trans
    (hn.tsum_le_tsum (fun i => norm_log_one_add_sub_le_sq (hhalf i))
      (summable_sq_norm_of_half_bound u hu hhalf))

/-- Comparing the product to the exponential of the signed sum gives a B-sized error. -/
theorem norm_tprod_one_add_sub_exp_tsum_le :
    ‖(∏' i, (1+u i))-Complex.exp (∑' i, u i)‖ ≤
      (∑' i, ‖u i‖^2)*Real.exp ((∑' i, ‖u i‖)+(∑' i, ‖u i‖^2)) := by
  have hz (i : ι) : 1+u i ≠ 0 := by
    intro h
    have he : u i = -1 := by linear_combination h
    have hh := hhalf i
    rw [he, norm_neg, norm_one] at hh
    norm_num at hh
  rw [← Complex.cexp_tsum_eq_tprod hz (Complex.summable_log_one_add_of_summable hu.of_norm)]
  let A := ∑' i, u i
  let R := (∑' i, Complex.log (1+u i))-A
  have he : Complex.exp (∑' i, Complex.log (1+u i))-Complex.exp A =
      Complex.exp A*(Complex.exp R-1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add,
      show A+R = ∑' i, Complex.log (1+u i) by dsimp [R]; ring]
  rw [he, norm_mul]
  have hA : ‖A‖ ≤ ∑' i, ‖u i‖ := norm_tsum_le_tsum_norm hu
  have hR : ‖R‖ ≤ ∑' i, ‖u i‖^2 := norm_tsum_log_one_add_sub_tsum_le u hu hhalf
  calc
    _ ≤ Real.exp (∑' i, ‖u i‖)*(‖R‖*Real.exp ‖R‖) :=
      mul_le_mul ((Complex.norm_exp_le_exp_norm A).trans (Real.exp_le_exp.mpr hA))
        (norm_exp_sub_one_le_norm_mul_exp R) (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (∑' i, ‖u i‖)*((∑' i, ‖u i‖^2)*Real.exp (∑' i, ‖u i‖^2)) := by gcongr
    _ = _ := by rw [Real.exp_add]; ring

/-- Lemma D.1, with exactly the printed constants and powers. -/
theorem norm_tprod_one_add_sub_one_le_signed_sum :
    ‖(∏' i, (1+u i))-1‖ ≤
      ‖∑' i, u i‖*Real.exp (∑' i, ‖u i‖)+
        (∑' i, ‖u i‖^2)*Real.exp ((∑' i, ‖u i‖)+(∑' i, ‖u i‖)^2) := by
  have he : (∏' i, (1+u i))-1 =
      ((∏' i, (1+u i))-Complex.exp (∑' i, u i))+(Complex.exp (∑' i, u i)-1) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hb := norm_tprod_one_add_sub_exp_tsum_le u hu hhalf
  have ha := norm_exp_sub_one_le_norm_mul_exp (∑' i, u i)
  have hS := norm_tsum_le_tsum_norm hu
  have hB := tsum_sq_norm_le_sq_tsum_norm u hu hhalf
  calc
    _ ≤ (∑' i, ‖u i‖^2)*Real.exp ((∑' i, ‖u i‖)+(∑' i, ‖u i‖^2))+
        ‖∑' i, u i‖*Real.exp ‖∑' i, u i‖ := add_le_add hb ha
    _ ≤ _ := by
      rw [add_comm]
      gcongr

/-- Remark D.3 with A interpreted as the complex sum in the subtracted linear term. -/
theorem norm_tprod_one_add_sub_one_sub_tsum_le_signed_square :
    ‖(∏' i, (1+u i))-1-(∑' i, u i)‖ ≤
      ‖∑' i, u i‖^2/2*Real.exp (∑' i, ‖u i‖)+
        (∑' i, ‖u i‖^2)*Real.exp ((∑' i, ‖u i‖)+(∑' i, ‖u i‖)^2) := by
  have he : (∏' i, (1+u i))-1-(∑' i, u i) =
      ((∏' i, (1+u i))-Complex.exp (∑' i, u i))+
        (Complex.exp (∑' i, u i)-1-(∑' i, u i)) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hb := norm_tprod_one_add_sub_exp_tsum_le u hu hhalf
  have ha := norm_exp_sub_one_sub_le_half_sq_mul_exp (∑' i, u i)
  have hS := norm_tsum_le_tsum_norm hu
  have hB := tsum_sq_norm_le_sq_tsum_norm u hu hhalf
  calc
    _ ≤ (∑' i, ‖u i‖^2)*Real.exp ((∑' i, ‖u i‖)+(∑' i, ‖u i‖^2))+
        ‖∑' i, u i‖^2/2*Real.exp ‖∑' i, u i‖ := add_le_add hb ha
    _ ≤ _ := by
      rw [add_comm]
      gcongr

omit hhalf in
/-- Both inequalities of Remark D.2, without needing the half-unit assumption. -/
theorem norm_tprod_one_add_sub_one_le_exp_sub_one_le :
    ‖(∏' i, (1+u i))-1‖ ≤ Real.exp (∑' i, ‖u i‖)-1 ∧
      Real.exp (∑' i, ‖u i‖)-1 ≤ (∑' i, ‖u i‖)*Real.exp (∑' i, ‖u i‖) :=
  ⟨norm_tprod_one_add_sub_one_le_exp u hu,
    exp_sub_one_le_mul_exp (tsum_nonneg (fun _ => norm_nonneg _))⟩

end NLS.ComplexAnalysis
