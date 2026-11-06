import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Algebraic passage from quadratic actions to coordinate estimates

Source: arXiv:1502.04550v1, Theorems 1 and 2, PDF/printed page 3.
These are conditional adapters, not the main analytic estimates. The physical
KdV Birkhoff map, its norm/action identity and its action bounds remain to be
constructed. The hypothesis `S² = 2*Q` records the exact convention
`I_n = (x_n²+y_n²)/2`.
-/

namespace NLS.Articles.KdVEstimates

/-- A squared action estimate yields a coordinate estimate with constant `2*C`. -/
theorem normBound_of_actionBound {S Q A B C : ℝ}
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hidentity : S ^ 2 = 2 * Q) (hbound : Q ≤ C ^ 2 * (A ^ 2 + B ^ 2)) :
    S ≤ 2 * C * (A + B) := by
  have hsum : A^2+B^2 ≤ (A+B)^2 := by nlinarith [mul_nonneg hA hB]
  have hbound' : Q ≤ C^2 * (A+B)^2 :=
    hbound.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg C))
  have hsq : S^2 ≤ (2*C*(A+B))^2 := by
    nlinarith [sq_nonneg (C*(A+B))]
  exact (sq_le_sq₀ hS (by positivity)).mp hsq

/-- Theorem 2(i) implies the displayed form of Theorem 1(i), once the
physical norm/action identity and action bound have been supplied. -/
theorem directSobolevBound_of_actionBound (m : ℕ) {S Q A b C : ℝ}
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hidentity : S^2 = 2*Q)
    (hbound : Q ≤ C^2 * (A^2 + (1+b)^(2*m) * b^2)) :
    S ≤ (2*C) * (A + (1+b)^m*b) := by
  apply normBound_of_actionBound hS hA (by positivity) hC hidentity
  convert hbound using 1
  ring

/-- Theorem 2(ii) gives the inverse form of Theorem 1(ii), with a harmless
constant enlargement. Both high and low norm/action normalizations are explicit. -/
theorem inverseSobolevBound_of_actionBound (m : ℕ) {A S b Q R D : ℝ}
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hb : 0 ≤ b) (hD : 0 ≤ D)
    (hhigh : S^2 = 2*Q) (hlow : b^2 = 2*R)
    (hbound : A^2 ≤ D^2 * (Q + (1+R)^m*R)) :
    A ≤ (2*D) * (S + (1+b)^m*b) := by
  have hR : 0 ≤ R := by nlinarith [sq_nonneg b]
  have hbase : 1+R ≤ (1+b)^2 := by nlinarith
  have hlow' : (1+R)^m*R ≤ ((1+b)^m*b)^2 := by
    calc
      (1+R)^m*R ≤ ((1+b)^2)^m*b^2 :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hbase m)
          (by nlinarith) hR (by positivity)
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm 2 m]
  have hmajor : A^2 ≤ D^2*(S^2+((1+b)^m*b)^2) := by
    apply hbound.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg D)
    exact add_le_add (by nlinarith [sq_nonneg S]) hlow'
  apply normBound_of_actionBound hA hS (by positivity) hD
    (Q := A^2/2) (by ring)
  have hnonneg : 0 ≤ D^2*(S^2+((1+b)^m*b)^2) := by positivity
  linarith

end NLS.Articles.KdVEstimates
