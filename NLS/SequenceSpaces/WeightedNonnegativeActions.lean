import NLS.SequenceSpaces.Weighted
import NLS.SequenceSpaces.NonnegativeActions
import Mathlib.Topology.Homeomorph.Lemmas

/-! # The nonnegative cone in weighted sequence spaces

Positivity concerns raw coefficients. Multiplication by any strictly
positive real weight identifies this cone homeomorphically with the
unweighted cone, preserving zero coordinates and all boundary points.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.WeightedCoeff
variable (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The source cone, defined using the original unweighted coefficients. -/
def nonnegativeLocus : Set (WeightedCoeff w p) :=
  {a | ∀ n, (a.val n).im = 0 ∧ 0 ≤ (a.val n).re}

omit [Fact (1 ≤ p)] in
/-- Positive weighting preserves and reflects the original cone. -/
theorem mem_nonnegativeLocus_iff (a : WeightedCoeff w p) :
    a ∈ nonnegativeLocus w p ↔ weightEquiv w p a ∈ Coeff.nonnegativeLocus p := by
  constructor
  · intro ha n
    simpa only [weightEquiv_apply,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,add_zero,sub_zero] using
      And.intro (by rw [(ha n).1,mul_zero] : w n*(a.val n).im = 0)
        (mul_nonneg (w.positive n).le (ha n).2)
  · intro ha n
    have hn := ha n
    simp only [weightEquiv_apply,Complex.mul_im,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,add_zero,sub_zero] at hn
    exact ⟨(mul_eq_zero.mp hn.1).resolve_left (ne_of_gt (w.positive n)),
      (mul_nonneg_iff_of_pos_left (w.positive n)).mp hn.2⟩

/-- The weighting isometry restricted to the entire nonnegative cone. -/
def nonnegativeHomeomorph : nonnegativeLocus w p ≃ₜ Coeff.nonnegativeLocus p :=
  (weightIsometry w p).toHomeomorph.subtype (mem_nonnegativeLocus_iff w p)

@[simp] theorem nonnegativeHomeomorph_val (x : nonnegativeLocus w p) :
    (nonnegativeHomeomorph w p x).val = weightEquiv w p x.val := rfl

@[simp] theorem nonnegativeHomeomorph_symm_val (x : Coeff.nonnegativeLocus p) :
    ((nonnegativeHomeomorph w p).symm x).val = (weightEquiv w p).symm x.val := rfl

omit [Fact (1 ≤ p)] in
/-- Zero is included for every weight and exponent. -/
theorem zero_mem_nonnegativeLocus : (0 : WeightedCoeff w p) ∈ nonnegativeLocus w p := by
  intro n
  simp

end NLS.WeightedCoeff
