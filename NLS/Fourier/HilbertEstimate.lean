import NLS.Fourier.HilbertSquare

/-!
# Quantitative Hilbert estimates and their unique completions

A finite-input estimate includes the exponent hypotheses and a uniform norm
bound. Density turns it into the ordinary and shifted operators on the whole
sequence space, retaining the exact finite reciprocal formulas.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Fourier

/-- A proved uniform finite-input Hilbert estimate at a finite Banach exponent. -/
structure HilbertEstimate (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  one_lt : 1 < p
  ne_top : p ≠ ⊤
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  finite_bound : ∀ a : ℤ →₀ ℂ,
    ‖finiteHilbertCoeffs one_lt a‖ ≤ bound * ‖Coeff.ofFinsupp (p := p) a‖

namespace HilbertEstimate
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (h : HilbertEstimate p)

/-- The unique continuous extension of the estimated finite-input transform. -/
def operator : Coeff p →L[ℂ] Coeff p :=
  (finiteHilbertCoeffs h.one_lt).extendOfNorm Coeff.ofFinsupp

theorem operator_finite_eq (a : ℤ →₀ ℂ) :
    h.operator (Coeff.ofFinsupp a) = finiteHilbertCoeffs h.one_lt a :=
  LinearMap.extendOfNorm_eq (f := finiteHilbertCoeffs h.one_lt)
    (e := Coeff.ofFinsupp (p := p)) (Coeff.denseRange_ofFinsupp h.ne_top)
    ⟨h.bound, h.finite_bound⟩ a

theorem operator_finite (a : ℤ →₀ ℂ) (n : ℤ) :
    h.operator (Coeff.ofFinsupp a) n = finiteHilbert a n := by
  rw [operator_finite_eq, finiteHilbertCoeffs_apply]

theorem norm_operator_le : ‖h.operator‖ ≤ h.bound :=
  LinearMap.opNorm_extendOfNorm_le (f := finiteHilbertCoeffs h.one_lt)
    (e := Coeff.ofFinsupp (p := p)) (Coeff.denseRange_ofFinsupp h.ne_top)
    h.bound_nonneg h.finite_bound

theorem norm_operator_apply_le (a : Coeff p) : ‖h.operator a‖ ≤ h.bound * ‖a‖ :=
  h.operator.le_of_opNorm_le h.norm_operator_le a

/-- The estimate constant and proof cannot change the completed operator. -/
theorem operator_unique (T : Coeff p →L[ℂ] Coeff p)
    (hT : ∀ a : ℤ →₀ ℂ, ∀ n, T (Coeff.ofFinsupp a) n = finiteHilbert a n) : T = h.operator := by
  have he : (T : Coeff p → Coeff p) = h.operator := by
    apply (Coeff.denseRange_ofFinsupp h.ne_top).equalizer T.continuous h.operator.continuous
    funext a
    apply lp.ext
    funext n
    exact (hT a n).trans (h.operator_finite a n).symm
  exact ContinuousLinearMap.ext (congrFun he)

theorem operator_eq (g : HilbertEstimate p) : h.operator = g.operator :=
  g.operator_unique h.operator h.operator_finite

/-- The normalized shifted transform obtained from the same estimate. -/
def shifted : Coeff p →L[ℂ] Coeff p :=
  ((Real.pi : ℂ)⁻¹) • (h.operator - hilbertCorrectionCLM)

def shiftedBound : ℝ := Real.pi⁻¹ * (h.bound + ‖hilbertCorrectionCoeffs‖)

theorem norm_shifted_apply_le (a : Coeff p) : ‖h.shifted a‖ ≤ h.shiftedBound * ‖a‖ := by
  change ‖((Real.pi : ℂ)⁻¹) • (h.operator a - hilbertCorrectionCLM a)‖ ≤ _
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ Real.pi⁻¹ * (‖h.operator a‖ + ‖hilbertCorrectionCLM a‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ Real.pi⁻¹ * (h.bound * ‖a‖ + ‖a‖ * ‖hilbertCorrectionCoeffs‖) := by
      gcongr
      · exact h.norm_operator_apply_le a
      · exact norm_hilbertCorrectionCLM_apply_le a
    _ = _ := by unfold shiftedBound; ring

theorem shifted_finite (a : ℤ →₀ ℂ) (n : ℤ) :
    h.shifted (Coeff.ofFinsupp a) n =
      a.sum (fun k z => z * (2 / ((Real.pi : ℂ) * (2 * k - 2 * n - 1)))) := by
  change (Real.pi : ℂ)⁻¹ * (h.operator (Coeff.ofFinsupp a) n -
    hilbertCorrectionCLM (Coeff.ofFinsupp (p := p) a) n) = _
  rw [operator_finite, hilbertCorrectionCLM_finite]
  have he : finiteHilbert a n = (Real.pi : ℂ) * shiftedHilbert (Coeff.ofFinsupp a) n +
      a.sum (fun k z => z * hilbertCorrection (n - k)) := by
    rw [← discreteHilbert_finite]
    change (Real.pi : ℂ) * shiftedHilbert (Coeff.ofFinsupp a) n +
      hilbertCorrectionCLM (Coeff.ofFinsupp (p := 2) a) n = _
    rw [hilbertCorrectionCLM_finite]
  rw [he, add_sub_cancel_right,
    inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), shiftedHilbert_finite]

end HilbertEstimate

/-- The already proved Hilbert-space estimate starts the doubling induction. -/
def hilbertEstimateTwo : HilbertEstimate 2 where
  one_lt := by norm_num
  ne_top := by simp
  bound := discreteHilbertBound
  bound_nonneg := discreteHilbertBound_pos.le
  finite_bound := norm_finiteHilbert_two_le

theorem hilbertEstimateTwo_operator : hilbertEstimateTwo.operator = discreteHilbert :=
  (hilbertEstimateTwo.operator_unique discreteHilbert discreteHilbert_finite).symm

end NLS.Fourier
