import NLS.SequenceSpaces.WeightedInfinityAnalyticRealization
import NLS.ComplexAnalysis.SharpExponentialRemainder
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! For any weight bounded below by one, exp(b)-1 is analytic in the
SAME weighted infinity space. All raw coefficients are the literal
scalar exponential remainders, with a local weighted norm bound. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

def weightedExpRemainder (w : Weight) (b : WeightedCoeff w ⊤) : WeightedCoeff w ⊤ :=
  ofFunctionOrZero w ⊤ (fun k => Complex.exp (b.val k) - 1)

private theorem weighted_exp_coefficient_bound (w : Weight) (hw : ∀ k, 1 ≤ w k)
    (b : WeightedCoeff w ⊤) (R : ℝ) (hR : ‖b‖ ≤ R) (k : ℤ) :
    w k * ‖Complex.exp (b.val k) - 1‖ ≤ R * Real.exp R := by
  have hc : w k * ‖b.val k‖ ≤ ‖b‖ := by
    simpa only [mul_comm] using (le_div_iff₀ (w.positive k)).mp (norm_apply_le w ⊤ b k)
  have h0 : ‖b.val k‖ ≤ R := by nlinarith [hw k,norm_nonneg (b.val k)]
  have he : ‖Complex.exp (b.val k) - 1‖ ≤ ‖b.val k‖ * Real.exp R :=
    (NLS.ComplexAnalysis.norm_exp_sub_one_le_norm_mul_exp _).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h0) (norm_nonneg _))
  calc
    _ ≤ w k * (‖b.val k‖ * Real.exp R) := mul_le_mul_of_nonneg_left he (w.positive k).le
    _ = (w k * ‖b.val k‖) * Real.exp R := by ring
    _ ≤ ‖b‖ * Real.exp R := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_right hR (Real.exp_pos _).le

private theorem local_weighted_exp_data (w : Weight) (hw : ∀ k, 1 ≤ w k) (b₀ : WeightedCoeff w ⊤) :
    ∃ U : Set (WeightedCoeff w ⊤), IsOpen U ∧ b₀ ∈ U ∧
      AnalyticOnNhd ℂ (weightedExpRemainder w) U ∧
        ∀ b ∈ U, ∀ k, (weightedExpRemainder w b).val k = Complex.exp (b.val k) - 1 := by
  let R := ‖b₀‖ + 1
  let U : Set (WeightedCoeff w ⊤) := ball 0 R
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hbU : b₀ ∈ U := by simp only [U,mem_ball,dist_zero_right,R]; linarith
  have h := analytic_infty_realization_of_weighted_bound w
    (fun b : WeightedCoeff w ⊤ => fun k => Complex.exp (b.val k) - 1) (U := U) isOpen_ball
    (fun k b _ => (((evalCLM w ⊤ k).analyticAt b).cexp').sub analyticAt_const)
    (R * Real.exp R) (mul_nonneg hR (Real.exp_pos _).le) (by
      intro b hb k
      have hbR : ‖b‖ ≤ R := (show ‖b‖ < R by simpa only [U,mem_ball,dist_zero_right] using hb).le
      exact weighted_exp_coefficient_bound w hw b R hbR k)
  exact ⟨U,isOpen_ball,hbU,h.1,fun b hb => (h.2 b hb).2⟩

theorem analyticAt_weightedExpRemainder (w : Weight) (hw : ∀ k, 1 ≤ w k) (b : WeightedCoeff w ⊤) :
    AnalyticAt ℂ (weightedExpRemainder w) b := by
  obtain ⟨U,_,hbU,ha,_⟩ := local_weighted_exp_data w hw b
  exact ha b hbU

theorem weightedExpRemainder_apply (w : Weight) (hw : ∀ k, 1 ≤ w k)
    (b : WeightedCoeff w ⊤) (k : ℤ) :
    (weightedExpRemainder w b).val k = Complex.exp (b.val k) - 1 := by
  obtain ⟨U,_,hbU,_,hraw⟩ := local_weighted_exp_data w hw b
  exact hraw b hbU k

theorem norm_weightedExpRemainder_le (w : Weight) (hw : ∀ k, 1 ≤ w k) (b : WeightedCoeff w ⊤) :
    ‖weightedExpRemainder w b‖ ≤ ‖b‖ * Real.exp ‖b‖ := by
  change ‖weightEquiv w ⊤ (weightedExpRemainder w b)‖ ≤ _
  apply lp.norm_le_of_forall_le (by positivity)
  intro k
  simpa only [weightEquiv_apply,weightedExpRemainder_apply w hw,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (w.positive k)] using weighted_exp_coefficient_bound w hw b ‖b‖ le_rfl k

end NLS.WeightedCoeff
