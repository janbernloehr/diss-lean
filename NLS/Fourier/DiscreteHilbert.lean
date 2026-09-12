import NLS.Fourier.ShiftedHilbert
import NLS.Fourier.HilbertKernel

/-!
# The ordinary discrete Hilbert transform

The ordinary transform in Appendix C is obtained from the shifted Hilbert
operator by an absolutely summable convolution correction. Its finite-input
formula includes the zero diagonal automatically through division by zero.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Fourier

/-- The source's ordinary transform on finite coefficients. -/
def finiteHilbert (a : ℤ →₀ ℂ) (n : ℤ) : ℂ := a.sum (fun k z => z / ((k : ℂ) - n))

theorem hilbertKernel_sub (n k : ℤ) : hilbertKernel (n - k) = 1 / ((k : ℂ) - n) := by
  unfold hilbertKernel
  rw [Int.cast_sub, show (n : ℂ) - k = -((k : ℂ) - n) by ring, inv_neg, neg_neg, one_div]

/-- The ordinary kernel belongs to each exponent needed for finite synthesis. -/
def hilbertKernelCoeffs {p : ℝ≥0∞} (hp : 1 < p) : Coeff p := ⟨hilbertKernel, hilbertKernel_memlp hp⟩

/-- Finite ordinary Hilbert synthesis, without yet asserting a uniform bound. -/
def finiteHilbertCoeffs {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) : (ℤ →₀ ℂ) →ₗ[ℂ] Coeff p :=
  Finsupp.linearCombination ℂ (fun k => Coeff.shift k (hilbertKernelCoeffs hp))

theorem finiteHilbertCoeffs_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (a : ℤ →₀ ℂ) (n : ℤ) :
    finiteHilbertCoeffs hp a n = finiteHilbert a n := by
  rw [finiteHilbertCoeffs, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, Coeff.shift_apply, hilbertKernelCoeffs, hilbertKernel_sub,
    mul_one_div, finiteHilbert]

theorem hilbertCorrectionCLM_finite {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : ℤ →₀ ℂ) (n : ℤ) :
    hilbertCorrectionCLM (Coeff.ofFinsupp (p := p) a) n =
      a.sum (fun k z => z * hilbertCorrection (n - k)) := by
  change Coeff.convolution (Coeff.ofFinsupp a) hilbertCorrectionCoeffs n = _
  rw [Coeff.convolution_apply]
  have he := (Equiv.subLeft n).tsum_eq (fun k : ℤ => (Coeff.ofFinsupp (p := p) a) (n - k) * hilbertCorrectionCoeffs k)
  simp only [Equiv.subLeft_apply, sub_sub_cancel, Coeff.ofFinsupp_apply, hilbertCorrectionCoeffs_apply] at he
  simp only [Coeff.ofFinsupp_apply, hilbertCorrectionCoeffs_apply]
  rw [← he]
  exact tsum_eq_sum fun k hk => by simp [Finsupp.notMem_support_iff.mp hk]

/-- The source's unnormalized ordinary transform, as a bounded Hilbert-space operator. -/
def discreteHilbert : Coeff 2 →L[ℂ] Coeff 2 :=
  (Real.pi : ℂ) • shiftedHilbert + hilbertCorrectionCLM

/-- A uniform constant for the ordinary Hilbert-space bound. -/
def discreteHilbertBound : ℝ := 2 * Real.pi + ‖hilbertCorrectionCoeffs‖

theorem discreteHilbertBound_pos : 0 < discreteHilbertBound := by
  unfold discreteHilbertBound
  positivity

theorem norm_discreteHilbert_apply_le (a : Coeff 2) :
    ‖discreteHilbert a‖ ≤ discreteHilbertBound * ‖a‖ := by
  change ‖(Real.pi : ℂ) • shiftedHilbert a + hilbertCorrectionCLM a‖ ≤ _
  calc
    _ ≤ ‖(Real.pi : ℂ) • shiftedHilbert a‖ + ‖hilbertCorrectionCLM a‖ := norm_add_le _ _
    _ = Real.pi * ‖shiftedHilbert a‖ + ‖hilbertCorrectionCLM a‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    _ ≤ Real.pi * (2 * ‖a‖) + ‖a‖ * ‖hilbertCorrectionCoeffs‖ := by
      gcongr
      · exact norm_shiftedHilbert_apply_le a
      · exact norm_hilbertCorrectionCLM_apply_le a
    _ = _ := by unfold discreteHilbertBound; ring

theorem discreteHilbert_finite (a : ℤ →₀ ℂ) (n : ℤ) :
    discreteHilbert (Coeff.ofFinsupp a) n = finiteHilbert a n := by
  change (Real.pi : ℂ) * shiftedHilbert (Coeff.ofFinsupp a) n +
    hilbertCorrectionCLM (Coeff.ofFinsupp (p := 2) a) n = _
  rw [shiftedHilbert_finite, hilbertCorrectionCLM_finite]
  unfold finiteHilbert Finsupp.sum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : (Real.pi : ℂ) * (2 / ((Real.pi : ℂ) * (2 * k - 2 * n - 1))) = shiftedKernel (n - k) := by
    unfold shiftedKernel
    push_cast
    have hd : 2 * (n : ℂ) - 2 * k + 1 = -(2 * (k : ℂ) - 2 * n - 1) := by ring
    rw [show 2 * ((n : ℂ) - k) + 1 = 2 * n - 2 * k + 1 by ring, hd]
    field_simp [hπ]
  rw [mul_left_comm (Real.pi : ℂ), he, hilbertCorrection]
  rw [hilbertKernel_sub]
  ring

theorem discreteHilbert_finite_eq (a : ℤ →₀ ℂ) :
    discreteHilbert (Coeff.ofFinsupp a) = finiteHilbertCoeffs (p := 2) (by norm_num) a := by
  apply lp.ext
  funext n
  rw [discreteHilbert_finite, finiteHilbertCoeffs_apply]

theorem norm_finiteHilbert_two_le (a : ℤ →₀ ℂ) :
    ‖finiteHilbertCoeffs (p := 2) (by norm_num) a‖ ≤ discreteHilbertBound * ‖Coeff.ofFinsupp (p := 2) a‖ := by
  rw [← discreteHilbert_finite_eq]
  exact norm_discreteHilbert_apply_le _

end NLS.Fourier
