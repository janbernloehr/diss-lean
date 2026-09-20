import NLS.Fourier.SampledProductEstimates

/-!
# Sampled relative-product errors on the free spectral discs

Rescaling by pi transfers the unit-lattice estimate to roots pi*k+a(k) and
arbitrary samples z(n) in the closed half-pi discs about pi*n. The omitted
factor at k=n is one, including at a free center where its raw quotient is
undefined. The remaining relative product has a uniform lp error bound.
-/

noncomputable section
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The displacement of a spectral sample, measured in lattice units. -/
def freeSampleDisplacement (z : ℤ → ℂ) (n : ℤ) : ℂ :=
  (z n-(Real.pi : ℂ)*n)/(Real.pi : ℂ)

/-- Half-pi discs give half-unit normalized sample displacements. -/
theorem norm_freeSampleDisplacement_le (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) (n : ℤ) :
    ‖freeSampleDisplacement z n‖ ≤ (1 : ℝ)/2 := by
  rw [freeSampleDisplacement, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact (div_le_iff₀ Real.pi_pos).mpr (by linarith [hz n])

/-- The relative product with the local factor omitted, minus one, in the original lp space. -/
def freeDiscProductError (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) : Coeff p :=
  sampledProductError hp1 hp (freeSampleDisplacement z) (norm_freeSampleDisplacement_le z hz)
    ((Real.pi : ℂ)⁻¹ • a)

/-- The coefficient is exactly the off-diagonal relative product of the spectral roots. -/
theorem freeDiscProductError_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) (n : ℤ) :
    freeDiscProductError hp1 hp a z hz n =
      (∏' k : ℤ, if k = n then 1 else
        ((Real.pi : ℂ)*k+a k-z n)/((Real.pi : ℂ)*k-z n))-1 := by
  rw [freeDiscProductError, sampledProductError_eq_relative_factors]
  congr 1
  apply tprod_congr
  intro k
  by_cases hkn : k = n
  · simp [hkn]
  simp only [if_neg hkn, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, freeSampleDisplacement]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn : (k : ℂ)+(Real.pi : ℂ)⁻¹*a k-(n+(z n-(Real.pi : ℂ)*n)/(Real.pi : ℂ)) =
      ((Real.pi : ℂ)*k+a k-z n)/(Real.pi : ℂ) := by field_simp; ring
  have hd : (k : ℂ)-(n+(z n-(Real.pi : ℂ)*n)/(Real.pi : ℂ)) =
      ((Real.pi : ℂ)*k-z n)/(Real.pi : ℂ) := by field_simp; ring
  rw [hn, hd, div_div_div_cancel_right₀ hπ]

/-- One norm-ball bound works for all spectral sampling sequences in the half-pi discs. -/
theorem norm_freeDiscProductError_le (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) {R : ℝ} (ha : ‖a‖ ≤ R) :
    ‖freeDiscProductError hp1 hp a z hz‖ ≤
      (hilbertTransformBound hp1 hp+‖hilbertSquareCoeffs‖)*(R/Real.pi)+
      Real.exp (absoluteSampledRowConstant hp*(R/Real.pi))*(absoluteSampledRowConstant hp*(R/Real.pi))^2 := by
  apply norm_sampledProductError_le
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr Real.pi_pos.le)

/-- Off-diagonal spectral relative products minus one form an lp sequence, uniformly bounded as above. -/
theorem memℓp_freeDisc_relative_product_sub_one (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (z : ℤ → ℂ)
    (hz : ∀ n : ℤ, ‖z n-(Real.pi : ℂ)*n‖ ≤ Real.pi/2) :
    Memℓp (fun n => (∏' k : ℤ, if k = n then 1 else
      ((Real.pi : ℂ)*k+a k-z n)/((Real.pi : ℂ)*k-z n))-1) p := by
  have h : Memℓp (fun n => freeDiscProductError hp1 hp a z hz n) p := lp.memℓp _
  simpa only [freeDiscProductError_apply] using h

end NLS.ZakharovShabat
