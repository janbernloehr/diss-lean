import NLS.Fourier.SampledProductMajorant
import NLS.ZakharovShabat.FreeDiscProductLp

/-!
# Common spectral-disc product majorants

One positive lp sequence bounds the omitted-diagonal product error at every
point of each closed half-pi disc, including its center and boundary.
-/

noncomputable section
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The off-diagonal relative spectral product on the nth free disc. -/
def freeDiscRelativeProduct (a : Coeff p) (n : ℤ) (z : ℂ) : ℂ :=
  ∏' k : ℤ, if k = n then 1 else ((Real.pi : ℂ)*k+a k-z)/((Real.pi : ℂ)*k-z)

/-- A positive lp majorant depending only on the spectral displacement sequence. -/
def freeDiscProductMajorant (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) : Coeff p :=
  sampledProductMajorant hp1 hp ((Real.pi : ℂ)⁻¹ • a)

/-- The same coefficient works at every point of its free disc. -/
theorem norm_freeDiscRelativeProduct_sub_one_le (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    ‖freeDiscRelativeProduct a n z-1‖ ≤ ‖freeDiscProductMajorant hp1 hp a n‖ := by
  let w : ℤ → ℂ := fun k => (Real.pi : ℂ)*k+(z-(Real.pi : ℂ)*n)
  have hw (k : ℤ) : ‖w k-(Real.pi : ℂ)*k‖ ≤ Real.pi/2 := by simpa [w] using hz
  have h := norm_sampledProductError_apply_le_majorant hp1 hp (freeSampleDisplacement w)
    (norm_freeSampleDisplacement_le w hw) ((Real.pi : ℂ)⁻¹ • a) n
  change ‖freeDiscProductError hp1 hp a w hw n‖ ≤ _ at h
  rw [freeDiscProductError_apply] at h
  simpa [freeDiscRelativeProduct, w, freeDiscProductMajorant] using h

/-- A uniform input-ball estimate for the common majorant. -/
theorem norm_freeDiscProductMajorant_le (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) {R : ℝ} (ha : ‖a‖ ≤ R) :
    ‖freeDiscProductMajorant hp1 hp a‖ ≤
      (hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*(R/Real.pi)+
      Real.exp (absoluteSampledRowConstant hp*(R/Real.pi))*(absoluteSampledRowConstant hp*(R/Real.pi))^2 := by
  apply norm_sampledProductMajorant_le
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr Real.pi_pos.le)

/-- The product itself is bounded throughout all the discs by one common finite number. -/
theorem norm_freeDiscRelativeProduct_le (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (n : ℤ) (z : ℂ) (hz : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    ‖freeDiscRelativeProduct a n z‖ ≤ 1+‖freeDiscProductMajorant hp1 hp a‖ := by
  calc
    _ ≤ ‖freeDiscRelativeProduct a n z-1‖+‖(1 : ℂ)‖ := norm_le_norm_sub_add _ _
    _ ≤ ‖freeDiscProductMajorant hp1 hp a n‖+1 :=
      add_le_add (norm_freeDiscRelativeProduct_sub_one_le hp1 hp a n z hz) (by simp)
    _ ≤ 1+‖freeDiscProductMajorant hp1 hp a‖ := by
      have h := lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' (freeDiscProductMajorant hp1 hp a) n
      linarith

end NLS.ZakharovShabat
