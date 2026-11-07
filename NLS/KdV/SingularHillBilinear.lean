import NLS.KdV.SingularHillPhysical

/-! # The bilinear Green identity for singular periodic Hill operators

The pairing is the full original H-minus-one/H1 duality, with its normalized
physical action and no complex conjugation. The potential is any original
complex H-minus-one distribution. This does not require an endpoint Fourier
bound or a finite source exponent.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
variable {L : ℝ} [Fact (0 < L)]

/-- Commutativity holds for the actual original H1 product. -/
theorem h1Product_comm (f g : FourierLebesgueSpace L 1 2) :
    h1Product f g = h1Product g f := by
  apply sobolevToWiener_injective (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
  rw [sobolevToWiener_h1Product, sobolevToWiener_h1Product, mul_comm]

end NLS.Fourier.PeriodicFourierLebesgue
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The original normalized bilinear H-minus-one/H1 pairing. -/
def singularHillPairing (v : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) : ℂ :=
  sobolevDualIsometry 1 (by norm_num) v f

theorem singularHillPairing_add_left (a b : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (a+b) f = singularHillPairing a f + singularHillPairing b f := by
  simp only [singularHillPairing, map_add, _root_.add_apply]

theorem singularHillPairing_smul_left (c : ℂ) (a : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (c • a) f = c * singularHillPairing a f := by
  simp only [singularHillPairing, map_smul, _root_.smul_apply, smul_eq_mul]

/-- The domain inclusion is symmetric for the physical bilinear pairing. -/
theorem singularHillDomainInclusion_bilinear (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (singularHillDomainInclusion f) g =
      singularHillPairing (singularHillDomainInclusion g) f := by
  simp only [singularHillPairing, sobolevDualIsometry_apply]
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ =>
    f.val (mode (-k)) * (singularHillDomainInclusion g).val (mode k))]
  apply tsum_congr
  intro k
  simpa only [Equiv.neg_apply, neg_neg, ← singularHillDomainInclusion_coefficient,
    singularHillDomainInclusion_val] using
    mul_comm (g.val (mode (-k))) (f.val (mode k))

/-- The free Laplacian has the original bilinear Green symmetry on its full domain. -/
theorem singularHillLaplacian_bilinear (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (singularHillLaplacian f) g =
      singularHillPairing (singularHillLaplacian g) f := by
  simp only [singularHillPairing, sobolevDualIsometry_apply]
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ =>
    f.val (mode (-k)) * (singularHillLaplacian g).val (mode k))]
  apply tsum_congr
  intro k
  simp only [Equiv.neg_apply, neg_neg]
  rw [show k = -(-k) by omega, singularHillLaplacian_coefficient,
    singularHillLaplacian_coefficient, freeHillValue_neg, neg_neg]
  simp only [neg_neg]
  ring

/-- Actual singular-potential multiplication is bilinearly symmetric. -/
theorem singularHillMultiplication_bilinear (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (hminusOneMultiplication q f) g =
      singularHillPairing (hminusOneMultiplication q g) f := by
  simp only [singularHillPairing, hminusOneMultiplication_apply, hminusOneProduct_duality]
  rw [h1Product_comm]

/-- The full original singular Hill operator satisfies the bilinear Green identity. -/
theorem singularHillOperator_bilinear (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (singularHillOperator q f) g =
      singularHillPairing (singularHillOperator q g) f := by
  change singularHillPairing (singularHillLaplacian f + hminusOneMultiplication q f) g =
    singularHillPairing (singularHillLaplacian g + hminusOneMultiplication q g) f
  rw [singularHillPairing_add_left, singularHillPairing_add_left,
    singularHillLaplacian_bilinear f g, singularHillMultiplication_bilinear q f g]

/-- The physical spectral pencil retains Green symmetry at every complex parameter. -/
theorem singularHillPencil_bilinear (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (f g : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPairing (z • singularHillDomainInclusion f - singularHillOperator q f) g =
      singularHillPairing (z • singularHillDomainInclusion g - singularHillOperator q g) f := by
  simp only [sub_eq_add_neg, ← neg_one_smul ℂ (singularHillOperator q f),
    ← neg_one_smul ℂ (singularHillOperator q g), singularHillPairing_add_left,
    singularHillPairing_smul_left]
  rw [singularHillDomainInclusion_bilinear f g, singularHillOperator_bilinear q f g]

end NLS.KdV
