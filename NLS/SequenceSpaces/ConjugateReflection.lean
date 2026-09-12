import NLS.SequenceSpaces.Reflection

/-!
# Complex conjugation of physical Fourier functions

Physical conjugation conjugates coefficients and reverses their indices.
It preserves every symmetric weighted coefficient space, including infinity.
-/

noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Conjugate reflection transported through a symmetric real weight. -/
def conjugateReflection (w : Weight) (_hw : ∀ k, w (-k) = w k)
    (a : WeightedCoeff w p) : WeightedCoeff w p :=
  (weightEquiv w p).symm (star (Coeff.reflection (weightEquiv w p a)))

@[simp] theorem conjugateReflection_apply (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a : WeightedCoeff w p) (k : ℤ) :
    (conjugateReflection w hw a).val k = (starRingEnd ℂ) (a.val (-k)) := by
  change star ((w (-k) : ℂ) * a.val (-k)) / (w k : ℂ) = _
  rw [hw]
  change (starRingEnd ℂ) ((w k : ℂ) * a.val (-k)) / (w k : ℂ) = _
  simp only [map_mul, Complex.conj_ofReal]
  exact mul_div_cancel_left₀ _ (w.complex_ne_zero k)

@[simp] theorem conjugateReflection_involutive (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a : WeightedCoeff w p) : conjugateReflection w hw (conjugateReflection w hw a) = a := by
  apply Subtype.ext
  funext k
  simp

@[simp] theorem norm_conjugateReflection (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a : WeightedCoeff w p) : ‖conjugateReflection w hw a‖ = ‖a‖ := by
  change ‖(weightIsometry w p).symm (star (Coeff.reflection (weightEquiv w p a)))‖ = _
  rw [(weightIsometry w p).symm.norm_map, norm_star, Coeff.reflection.norm_map]
  rfl

/-- Conjugating a Fourier convolution reverses and conjugates both factors. -/
theorem conj_tsum_convolution (a b : ℤ → ℂ) (k : ℤ) :
    (starRingEnd ℂ) (∑' j : ℤ, a (-k-j) * b j) =
      ∑' j : ℤ, (starRingEnd ℂ) (a (-(k-j))) * (starRingEnd ℂ) (b (-j)) := by
  rw [Complex.conj_tsum, ← (Equiv.neg ℤ).tsum_eq (fun j : ℤ =>
    (starRingEnd ℂ) (a (-(k-j))) * (starRingEnd ℂ) (b (-j)))]
  apply tsum_congr
  intro j
  simp only [map_mul, Equiv.neg_apply, neg_neg]
  rw [show -(k - -j) = -k - j by omega]

end NLS.WeightedCoeff
