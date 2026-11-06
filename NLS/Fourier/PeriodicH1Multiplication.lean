import NLS.SequenceSpaces.SobolevConvolutionBounds
import NLS.Fourier.PeriodicSobolevDuality
import NLS.Fourier.PeriodicSobolevEmbedding
import NLS.Fourier.PeriodicDistributionConvolutionProduct

/-! # H1 multiplication and its H-minus-one transpose

The H1 product is the actual pointwise product of the continuous periodic
representatives. Transposition through the full original Sobolev duality
defines multiplication of an H-minus-one potential by an H1 function.
All distributions act complex-linearly on tests: the native formula is
`(q*f)(g) = q(f*g)`. The normalization is the original factor 1/L.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

/-- Product in the original one-derivative Hilbert distribution space. -/
def h1Product (f g : FourierLebesgueSpace L 1 2) : FourierLebesgueSpace L 1 2 :=
  (sobolevCoefficients 1 2).symm
    (NLS.ZakharovShabat.sobolevConvolution (by norm_num)
      (sobolevCoefficients 1 2 f) (sobolevCoefficients 1 2 g))

/-- The original H1 product has the genuinely summed normalized coefficients. -/
theorem h1Product_coefficient (f g : FourierLebesgueSpace L 1 2) (n : ℤ) :
    (h1Product f g).val (mode (-n)) =
      ∑' k : ℤ, f.val (mode (-(n-k))) * g.val (mode (-k)) := by
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm _)).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply, NLS.ZakharovShabat.sobolevConvolution_apply]
  rfl

/-- The original H1 product agrees with multiplication in the Wiener algebra. -/
theorem sobolevToWiener_h1Product (f g : FourierLebesgueSpace L 1 2) :
    sobolevToWiener (by norm_num) (h1Product f g) =
      sobolevToWiener (by norm_num) f * sobolevToWiener (by norm_num) g := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  change _ = (youngProduct youngRelation_wiener _ _).val (mode (-n))
  simp only [sobolevToWiener_coefficient, h1Product_coefficient, youngProduct_coefficient]

/-- In particular this is the actual pointwise product on the physical circle. -/
theorem continuousRepresentative_h1Product (f g : FourierLebesgueSpace L 1 2) :
    continuousRepresentative (sobolevToWiener (by norm_num) (h1Product f g)) =
      continuousRepresentative (sobolevToWiener (by norm_num) f) *
        continuousRepresentative (sobolevToWiener (by norm_num) g) := by
  rw [sobolevToWiener_h1Product, continuousRepresentative_mul]

/-- A finite product bound in the original H1 norm. -/
theorem norm_h1Product_le (f g : FourierLebesgueSpace L 1 2) :
    ‖h1Product f g‖ ≤
      (3*WeightedCoeff.sobolevEmbeddingConstant 2 (by norm_num))*‖f‖*‖g‖ := by
  simpa only [h1Product, LinearIsometryEquiv.norm_map] using
    WeightedCoeff.norm_sobolevConvolution_le (by norm_num)
      (sobolevCoefficients 1 2 f) (sobolevCoefficients 1 2 g)

/-- Additivity of the actual H1 product in its first factor. -/
theorem h1Product_add_left (f f' g : FourierLebesgueSpace L 1 2) :
    h1Product (f+f') g = h1Product f g + h1Product f' g := by
  simp only [h1Product, map_add, WeightedCoeff.sobolevConvolution_add_left]

/-- Additivity of the actual H1 product in its second factor. -/
theorem h1Product_add_right (f g g' : FourierLebesgueSpace L 1 2) :
    h1Product f (g+g') = h1Product f g + h1Product f g' := by
  simp only [h1Product, map_add, WeightedCoeff.sobolevConvolution_add_right]

/-- Scalar compatibility in the first factor. -/
theorem h1Product_smul_left (c : ℂ) (f g : FourierLebesgueSpace L 1 2) :
    h1Product (c • f) g = c • h1Product f g := by
  simp only [h1Product, map_smul, WeightedCoeff.sobolevConvolution_smul_left]

/-- Scalar compatibility in the second factor. -/
theorem h1Product_smul_right (c : ℂ) (f g : FourierLebesgueSpace L 1 2) :
    h1Product f (c • g) = c • h1Product f g := by
  simp only [h1Product, map_smul, WeightedCoeff.sobolevConvolution_smul_right]

/-- Bounded bilinear physical multiplication in the original H1 space. -/
def h1ProductCLM : FourierLebesgueSpace L 1 2 →L[ℂ]
    FourierLebesgueSpace L 1 2 →L[ℂ] FourierLebesgueSpace L 1 2 :=
  (LinearMap.mk₂ ℂ h1Product h1Product_add_left h1Product_smul_left
    h1Product_add_right h1Product_smul_right).mkContinuous₂
      (3*WeightedCoeff.sobolevEmbeddingConstant 2 (by norm_num))
        (fun f g => by simpa only [LinearMap.mk₂_apply] using norm_h1Product_le f g)

@[simp] theorem h1ProductCLM_apply (f g : FourierLebesgueSpace L 1 2) :
    h1ProductCLM f g = h1Product f g := rfl

/-- Multiplication of a singular potential, defined on the full H1 domain
by transposition of actual physical multiplication. -/
def hminusOneProduct (q : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) : FourierLebesgueSpace L (-1) 2 :=
  (sobolevDualIsometry 1 (by norm_num)).symm
    ((sobolevDualIsometry 1 (by norm_num) q).comp (h1ProductCLM f))

/-- The defining duality identity holds for every original H1 test. -/
theorem hminusOneProduct_duality (q : FourierLebesgueSpace L (-1) 2)
    (f g : FourierLebesgueSpace L 1 2) :
    sobolevDualIsometry 1 (by norm_num) (hminusOneProduct q f) g =
      sobolevDualIsometry 1 (by norm_num) q (h1Product f g) := by
  change (sobolevDualIsometry 1 (by norm_num)
    ((sobolevDualIsometry 1 (by norm_num)).symm _)) g = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- On original smooth tests, the transpose is exactly the normalized
distributional action of the singular product. -/
theorem hminusOneProduct_apply (q : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) (g : SmoothPeriodicTest L) :
    (hminusOneProduct q f).val g =
      sobolevDualIsometry 1 (by norm_num) q (h1Product f (ofSmooth 1 2 g)) := by
  rw [← sobolevDualIsometry_ofSmooth (p := 2) (q := 2) 1 (by norm_num)
    (hminusOneProduct q f) g, hminusOneProduct_duality]

/-- The transposed product is bounded in the original H-minus-one norm. -/
theorem norm_hminusOneProduct_le (q : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) :
    ‖hminusOneProduct q f‖ ≤
      (3*WeightedCoeff.sobolevEmbeddingConstant 2 (by norm_num))*‖q‖*‖f‖ := by
  have hC := WeightedCoeff.sobolevEmbeddingConstant_nonneg 2 (by norm_num)
  rw [← (sobolevDualIsometry (L := L) (p := 2) 1 (by norm_num)).norm_map
    (hminusOneProduct q f)]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro g
  rw [hminusOneProduct_duality]
  apply ((sobolevDualIsometry 1 (by norm_num) q).le_opNorm _).trans
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖q‖*((3*WeightedCoeff.sobolevEmbeddingConstant 2 (by norm_num))*‖f‖*‖g‖) := by
      apply mul_le_mul_of_nonneg_left (norm_h1Product_le f g) (norm_nonneg q)
    _ = _ := by ring

/-- The transposed physical product is additive in its H1 input. -/
theorem hminusOneProduct_add_right (q : FourierLebesgueSpace L (-1) 2)
    (f g : FourierLebesgueSpace L 1 2) :
    hminusOneProduct q (f+g) = hminusOneProduct q f + hminusOneProduct q g := by
  apply (sobolevDualIsometry (p := 2) (q := 2) 1 (by norm_num)).injective
  ext b
  simp only [map_add, _root_.add_apply, hminusOneProduct_duality,
    h1Product_add_left]

/-- The transposed physical product is linear in its H1 input. -/
theorem hminusOneProduct_smul_right (q : FourierLebesgueSpace L (-1) 2)
    (c : ℂ) (f : FourierLebesgueSpace L 1 2) :
    hminusOneProduct q (c • f) = c • hminusOneProduct q f := by
  apply (sobolevDualIsometry (p := 2) (q := 2) 1 (by norm_num)).injective
  ext b
  simp only [map_smul, _root_.smul_apply, hminusOneProduct_duality,
    h1Product_smul_left]

/-- The actual multiplication operator V_q from the full original H1 domain
to the original H-minus-one space, for every singular H-minus-one potential. -/
def hminusOneMultiplication (q : FourierLebesgueSpace L (-1) 2) :
    FourierLebesgueSpace L 1 2 →L[ℂ] FourierLebesgueSpace L (-1) 2 :=
  LinearMap.mkContinuous
    { toFun := hminusOneProduct q
      map_add' := hminusOneProduct_add_right q
      map_smul' := hminusOneProduct_smul_right q }
    ((3*WeightedCoeff.sobolevEmbeddingConstant 2 (by norm_num))*‖q‖)
      (norm_hminusOneProduct_le q)

@[simp] theorem hminusOneMultiplication_apply (q : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) :
    hminusOneMultiplication q f = hminusOneProduct q f := rfl

/-- Original Fourier modes have their exact unit single coefficients in H1. -/
theorem ofSmooth_h1_mode_coefficient (k n : ℤ) :
    (ofSmooth 1 2 (mode k : SmoothPeriodicTest L)).val (mode (-n)) =
      if n = k then 1 else 0 := by
  have he : (ofSmooth 1 2 (mode k : SmoothPeriodicTest L)).val =
      Distribution.ofContinuous (fourier k) := by
    change Distribution.ofL1 (mode k) _ =
      Distribution.ofL1 (fun x : ℝ => fourier k (x : AddCircle L)) _
    congr 1
    funext x
    rw [mode_apply_physical, fourier_coe_apply]
    congr 1
    ring
  rw [he, Distribution.ofContinuous_fourier_coefficient]

/-- Multiplication by a physical mode is exactly a Fourier index shift. -/
theorem h1Product_mode_coefficient (f : FourierLebesgueSpace L 1 2) (k n : ℤ) :
    (h1Product f (ofSmooth 1 2 (mode k))).val (mode (-n)) =
      f.val (mode (-(n-k))) := by
  rw [h1Product_coefficient]
  simp only [ofSmooth_h1_mode_coefficient, mul_ite, mul_one, mul_zero, tsum_ite_eq]

/-- The transpose of actual multiplication has the source's exact Fourier
convolution formula, for all H-minus-one potentials and all H1 inputs. -/
theorem hminusOneProduct_coefficient (q : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) (m : ℤ) :
    (hminusOneProduct q f).val (mode (-m)) =
      ∑' k : ℤ, q.val (mode (-(m-k))) * f.val (mode (-k)) := by
  rw [hminusOneProduct_apply, sobolevDualIsometry_apply]
  simp only [h1Product_mode_coefficient, sub_neg_eq_add]
  rw [← (Equiv.addRight m).tsum_eq (fun k : ℤ =>
    q.val (mode (-(m-k))) * f.val (mode (-k)))]
  apply tsum_congr
  intro n
  change f.val (mode (-(n+m))) * q.val (mode n) =
    q.val (mode (-(m-(n+m)))) * f.val (mode (-(n+m)))
  rw [show -(m-(n+m)) = n by omega]
  exact mul_comm _ _

/-- Every Fourier convolution above is absolutely convergent, as a consequence
of the full original Sobolev duality, rather than a totalized-sum definition. -/
theorem summable_norm_hminusOneProduct_terms (q : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) (m : ℤ) :
    Summable (fun k : ℤ => ‖q.val (mode (-(m-k))) * f.val (mode (-k))‖) := by
  have hs := sobolevDualIsometry_summable 1 q (h1Product f (ofSmooth 1 2 (mode (-m))))
  simp only [h1Product_mode_coefficient, sub_neg_eq_add] at hs
  have ht := hs.comp_injective (Equiv.addRight (-m)).injective
  apply ht.congr
  intro k
  change ‖f.val (mode (-(k + -m + m))) * q.val (mode (k + -m))‖ = _
  rw [show k + -m + m = k by omega, show k + -m = -(m-k) by omega, mul_comm]

/-- Multiplication defined by physical H1 duality satisfies the genuinely
convergent original-distribution Fourier product criterion. -/
theorem hasFourierProduct_hminusOneProduct (q : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) :
    Distribution.HasFourierProduct q.val f.val (hminusOneProduct q f).val := by
  intro m
  rw [hminusOneProduct_coefficient]
  exact (summable_norm_hminusOneProduct_terms q f m).of_norm.hasSum

end NLS.Fourier.PeriodicFourierLebesgue
