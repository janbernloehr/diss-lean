import NLS.Fourier.NativePeriodicConjugation
import NLS.Fourier.PeriodicH1Multiplication

/-!
# Native conjugation, full Sobolev duality and singular multiplication

Every operation is on the original smooth-test distributions. Conjugation
is an isometry for every real order and exponent, and the full H1 product
and its H-minus-one transpose respect this same physical conjugation.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

/-- Native physical conjugation as a conjugate-linear isometric involution. -/
def sobolevConjugation (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    FourierLebesgueSpace L s p ≃ₗᵢ⋆[ℂ] FourierLebesgueSpace L s p where
  toFun := conjugate (Weight.sobolev s) (Weight.sobolev_neg s)
  invFun := conjugate (Weight.sobolev s) (Weight.sobolev_neg s)
  left_inv u := Subtype.ext (Distribution.conjugate_conjugate u.val)
  right_inv u := Subtype.ext (Distribution.conjugate_conjugate u.val)
  map_add' u v := by
    apply Subtype.ext
    ext f
    change star (u.val f.conjugate+v.val f.conjugate) =
      star (u.val f.conjugate)+star (v.val f.conjugate)
    exact star_add _ _
  map_smul' c u := by
    apply Subtype.ext
    ext f
    change star (c*u.val f.conjugate) = star c*star (u.val f.conjugate)
    rw [star_mul]
    ring
  norm_map' := norm_conjugate (Weight.sobolev s) (Weight.sobolev_neg s)

@[simp] theorem sobolevConjugation_val (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : FourierLebesgueSpace L s p) :
    (sobolevConjugation s p u).val = u.val.conjugate := rfl

@[simp] theorem sobolevConjugation_coefficient (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : FourierLebesgueSpace L s p) (k : ℤ) :
    (sobolevConjugation s p u).val (mode (-k)) = star (u.val (mode k)) :=
  Distribution.conjugate_coefficient u.val k

/-- The same native coefficient identity without a negated test index. -/
theorem sobolevConjugation_mode (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : FourierLebesgueSpace L s p) (k : ℤ) :
    (sobolevConjugation s p u).val (mode k) = star (u.val (mode (-k))) := by
  simpa only [neg_neg] using sobolevConjugation_coefficient s p u (-k)

@[simp] theorem sobolevConjugation_involutive (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : FourierLebesgueSpace L s p) :
    sobolevConjugation s p (sobolevConjugation s p u) = u :=
  (sobolevConjugation s p).symm_apply_apply u

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Conjugating both original Sobolev dual inputs conjugates the actual normalized action. -/
theorem sobolevDualIsometry_conjugation (s : ℝ) (hp : p ≠ ⊤)
    (v : FourierLebesgueSpace L (-s) q) (u : FourierLebesgueSpace L s p) :
    sobolevDualIsometry s hp (sobolevConjugation (-s) q v) (sobolevConjugation s p u) =
      star (sobolevDualIsometry s hp v u) := by
  simp only [sobolevDualIsometry_apply, sobolevConjugation_mode, neg_neg, Complex.star_def]
  rw [Complex.conj_tsum, ← (Equiv.neg ℤ).tsum_eq
    (fun n : ℤ => (starRingEnd ℂ) (u.val (mode (-n))*v.val (mode n)))]
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply, neg_neg, map_mul]

/-- One-sided conjugation identity for the full original continuous dual. -/
theorem sobolevDualIsometry_conjugate_left (s : ℝ) (hp : p ≠ ⊤)
    (v : FourierLebesgueSpace L (-s) q) (u : FourierLebesgueSpace L s p) :
    sobolevDualIsometry s hp (sobolevConjugation (-s) q v) u =
      star (sobolevDualIsometry s hp v (sobolevConjugation s p u)) := by
  simpa only [sobolevConjugation_involutive] using
    sobolevDualIsometry_conjugation s hp v (sobolevConjugation s p u)

/-- The full physical H1 product respects native distributional conjugation. -/
theorem h1Product_conjugation (f g : FourierLebesgueSpace L 1 2) :
    sobolevConjugation 1 2 (h1Product f g) =
      h1Product (sobolevConjugation 1 2 f) (sobolevConjugation 1 2 g) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  have hc := h1Product_coefficient f g (-k)
  simp only [neg_neg] at hc
  rw [sobolevConjugation_coefficient, hc, h1Product_coefficient]
  simp only [sobolevConjugation_coefficient]
  simpa only [neg_neg, starRingEnd_apply] using WeightedCoeff.conj_tsum_convolution
    (fun j => f.val (mode (-j))) (fun j => g.val (mode (-j))) k

/-- Transposed multiplication by every original H-minus-one potential respects
the same physical conjugation, with no extra regularity premise. -/
theorem hminusOneProduct_conjugation (v : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) :
    sobolevConjugation (-1) 2 (hminusOneProduct v f) =
      hminusOneProduct (sobolevConjugation (-1) 2 v) (sobolevConjugation 1 2 f) := by
  apply (sobolevDualIsometry 1 (by norm_num : (2:ℝ≥0∞) ≠ ⊤)).injective
  apply ContinuousLinearMap.ext
  intro g
  rw [sobolevDualIsometry_conjugate_left, hminusOneProduct_duality,
    hminusOneProduct_duality, sobolevDualIsometry_conjugate_left,
    h1Product_conjugation, sobolevConjugation_involutive]

end NLS.Fourier.PeriodicFourierLebesgue
