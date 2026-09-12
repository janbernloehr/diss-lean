import NLS.SequenceSpaces.Basic
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Complex-linear testing of bounded coefficient sequences

Unlike the Hermitian pairing, this duality is linear in the test sequence as
well as the coefficient sequence. It is the convention needed for complex
Schwartz distributions.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The unconjugated pairing is absolutely convergent. -/
theorem summable_norm_testPairing (a : Coeff p) (b : Coeff 1) :
    Summable (fun n : ℤ => ‖a n * b n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => ?_) ((lp.memℓp b).norm.summable_of_one.mul_left ‖a‖)
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' a n) (norm_nonneg _)

/-- Duality with `ℓ¹` tests, without complex conjugation. -/
def testPairing (a : Coeff p) (b : Coeff 1) : ℂ := ∑' n : ℤ, a n * b n

theorem norm_testPairing_le (a : Coeff p) (b : Coeff 1) :
    ‖testPairing a b‖ ≤ ‖a‖ * ‖b‖ := by
  calc
    _ ≤ ∑' n : ℤ, ‖a n * b n‖ := norm_tsum_le_tsum_norm (summable_norm_testPairing a b)
    _ ≤ ∑' n : ℤ, ‖a‖ * ‖b n‖ := by
      apply (summable_norm_testPairing a b).tsum_le_tsum
      · intro n
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          (lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' a n) (norm_nonneg _)
      · exact (lp.memℓp b).norm.summable_of_one.mul_left ‖a‖
    _ = _ := by
      have hb : (∑' n : ℤ, ‖b n‖) = ‖b‖ := by
        simpa using (lp.hasSum_norm (p := 1) (by simp) b).tsum_eq
      rw [tsum_mul_left, hb]

/-- A coefficient sequence is a bounded linear functional on `ℓ¹` tests. -/
def testFunctional (a : Coeff p) : Coeff 1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := testPairing a
      map_add' := fun b c => by
        change (∑' n, a n * (b n + c n)) = _
        simp_rw [mul_add]
        exact (summable_norm_testPairing a b).of_norm.tsum_add
          (summable_norm_testPairing a c).of_norm
      map_smul' := fun z b => by
        change (∑' n, a n * (z * b n)) = z * _
        simp_rw [mul_left_comm (a _) z]
        exact tsum_mul_left }
    ‖a‖ (norm_testPairing_le a)

@[simp] theorem testFunctional_apply (a : Coeff p) (b : Coeff 1) :
    testFunctional a b = ∑' n : ℤ, a n * b n := rfl

theorem testFunctional_add (a c : Coeff p) :
    testFunctional (a + c) = testFunctional a + testFunctional c := by
  ext b
  change (∑' n, (a n + c n) * b n) = _
  simp_rw [add_mul]
  exact (summable_norm_testPairing a b).of_norm.tsum_add
    (summable_norm_testPairing c b).of_norm

theorem testFunctional_smul (z : ℂ) (a : Coeff p) :
    testFunctional (z • a) = z • testFunctional a := by
  ext b
  change (∑' n, (z * a n) * b n) = z * _
  simp_rw [mul_assoc]
  exact tsum_mul_left

/-- The coefficient-to-dual map is continuous in operator norm. -/
def testDualityCLM : Coeff p →L[ℂ] Coeff 1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := testFunctional
      map_add' := testFunctional_add
      map_smul' := testFunctional_smul }
    1 (fun a => by
      simpa using (testFunctional a).opNorm_le_bound (norm_nonneg a) (norm_testPairing_le a))

@[simp] theorem testDualityCLM_apply (a : Coeff p) (b : Coeff 1) :
    testDualityCLM a b = testPairing a b := rfl

/-- A single mode tests exactly the matching coordinate. -/
@[simp] theorem testFunctional_single (n : ℤ) (c : ℂ) (b : Coeff 1) :
    testFunctional (lp.single p n c) b = c * b n := by
  classical
  simp [testFunctional_apply, lp.single_apply, Pi.single_apply]

end NLS.Coeff
