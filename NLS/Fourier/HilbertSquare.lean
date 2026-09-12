import NLS.Fourier.CotlarIdentity

/-!
# The summable square kernel in the Cotlar identity

The diagonal remainder is convolution with the square of the ordinary
Hilbert kernel. It is bounded on every Banach `ℓp` space by Young's inequality.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier

/-- The square kernel is absolutely summable. -/
theorem hilbertKernel_square_memlp_one : Memℓp (fun j => (hilbertKernel j)^2) 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, norm_pow]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (hilbertKernel_memlp (p := 2) (by norm_num)).summable (by norm_num)

/-- The diagonal remainder kernel as an absolutely summable sequence. -/
def hilbertSquareCoeffs : Coeff 1 := ⟨fun j => (hilbertKernel j)^2, hilbertKernel_square_memlp_one⟩

@[simp] theorem hilbertSquareCoeffs_apply (j : ℤ) : hilbertSquareCoeffs j = (hilbertKernel j)^2 := rfl

/-- The square-kernel operator at every Banach exponent. -/
def hilbertSquare {p : ℝ≥0∞} [Fact (1 ≤ p)] : Coeff p →L[ℂ] Coeff p :=
  Coeff.convolutionCLM.flip hilbertSquareCoeffs

theorem norm_hilbertSquare_apply_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : Coeff p) :
    ‖hilbertSquare a‖ ≤ ‖a‖ * ‖hilbertSquareCoeffs‖ := Coeff.norm_convolution_le _ _

/-- The remainder operator agrees with the finite rational expression in the identity. -/
theorem hilbertSquare_finite {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : ℤ →₀ ℂ) (n : ℤ) :
    hilbertSquare (Coeff.ofFinsupp (p := p) a) n = finiteHilbertSquare a n := by
  change Coeff.convolution (Coeff.ofFinsupp a) hilbertSquareCoeffs n = _
  rw [Coeff.convolution_ofFinsupp_apply]
  unfold finiteHilbertSquare
  apply Finsupp.sum_congr
  intro k hk
  simp only [hilbertSquareCoeffs_apply, hilbertKernel_sub, ← inv_pow, div_eq_mul_inv, one_mul]

end NLS.Fourier
