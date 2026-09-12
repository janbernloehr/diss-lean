import NLS.Fourier.HilbertSquare
import NLS.SequenceSpaces.QuarticProduct

/-!
# Bounded ordinary and shifted Hilbert transforms on `ℓ4`

The discrete Cotlar identity, the proved `ℓ2` bound, and Hölder give a uniform
quartic estimate. Density then constructs the operators on all `ℓ4` inputs.
This is a first exponent-doubling step, not the full range of Appendix C.1.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Fourier
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The quadratic estimate obtained from the discrete cancellation identity. -/
theorem finiteHilbert_quartic_quadratic (a : ℤ →₀ ℂ) :
    ‖finiteHilbertCoeffs (p := 4) (by norm_num) a‖^2 ≤
      2 * discreteHilbertBound * ‖Coeff.ofFinsupp (p := 4) a‖ *
        ‖finiteHilbertCoeffs (p := 4) (by norm_num) a‖ +
      3 * ‖hilbertSquareCoeffs‖ * ‖Coeff.ofFinsupp (p := 4) a‖^2 := by
  let u : Coeff 4 := Coeff.ofFinsupp a
  let v : Coeff 4 := finiteHilbertCoeffs (by norm_num) a
  let w : Coeff 2 := Coeff.ofFinsupp (finiteProduct a (finiteHilbert a))
  let s : Coeff 2 := Coeff.ofFinsupp (finiteProduct a a)
  have hw : w = Coeff.quarticProduct u v := by
    apply lp.ext
    funext n
    simp only [w, u, v, Coeff.ofFinsupp_apply, finiteProduct_apply,
      Coeff.quarticProduct_apply, finiteHilbertCoeffs_apply]
  have hs : s = Coeff.quarticProduct u u := by
    apply lp.ext
    funext n
    rfl
  have he : Coeff.quarticProduct v v =
      (2 : ℂ) • discreteHilbert w + hilbertSquare s +
        (2 : ℂ) • Coeff.quarticProduct u (hilbertSquare u) := by
    apply lp.ext
    funext n
    change v n * v n = 2 * discreteHilbert w n + hilbertSquare s n +
      2 * (u n * hilbertSquare u n)
    simp only [u, v, w, s, finiteHilbertCoeffs_apply, discreteHilbert_finite,
      hilbertSquare_finite, Coeff.ofFinsupp_apply]
    simpa only [pow_two, mul_assoc] using finiteHilbert_cotlar a n
  have hwbound : ‖w‖ ≤ ‖u‖ * ‖v‖ := by rw [hw]; exact Coeff.norm_quarticProduct_le u v
  have hsbound : ‖s‖ = ‖u‖^2 := by rw [hs, Coeff.norm_quarticProduct_self]
  have hH : ‖discreteHilbert w‖ ≤ discreteHilbertBound * (‖u‖ * ‖v‖) :=
    (norm_discreteHilbert_apply_le w).trans
      (mul_le_mul_of_nonneg_left hwbound discreteHilbertBound_pos.le)
  have hR : ‖hilbertSquare s‖ ≤ ‖u‖^2 * ‖hilbertSquareCoeffs‖ := by
    simpa only [hsbound] using norm_hilbertSquare_apply_le s
  have hP : ‖Coeff.quarticProduct u (hilbertSquare u)‖ ≤ ‖u‖ * (‖u‖ * ‖hilbertSquareCoeffs‖) :=
    (Coeff.norm_quarticProduct_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_hilbertSquare_apply_le u) (norm_nonneg u))
  change ‖v‖^2 ≤ 2 * discreteHilbertBound * ‖u‖ * ‖v‖ + 3 * ‖hilbertSquareCoeffs‖ * ‖u‖^2
  calc
    _ = ‖Coeff.quarticProduct v v‖ := (Coeff.norm_quarticProduct_self v).symm
    _ = ‖(2 : ℂ) • discreteHilbert w + hilbertSquare s +
        (2 : ℂ) • Coeff.quarticProduct u (hilbertSquare u)‖ := by rw [he]
    _ ≤ ‖(2 : ℂ) • discreteHilbert w‖ + ‖hilbertSquare s‖ +
        ‖(2 : ℂ) • Coeff.quarticProduct u (hilbertSquare u)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = 2 * ‖discreteHilbert w‖ + ‖hilbertSquare s‖ +
        2 * ‖Coeff.quarticProduct u (hilbertSquare u)‖ := by simp only [norm_smul]; norm_num
    _ ≤ 2 * (discreteHilbertBound * (‖u‖ * ‖v‖)) + ‖u‖^2 * ‖hilbertSquareCoeffs‖ +
        2 * (‖u‖ * (‖u‖ * ‖hilbertSquareCoeffs‖)) := by gcongr
    _ = _ := by ring

/-- One explicit constant furnished by the quadratic inequality. -/
def quarticHilbertBound : ℝ := 2 * discreteHilbertBound + 3 * ‖hilbertSquareCoeffs‖ + 1

theorem quarticHilbertBound_pos : 0 < quarticHilbertBound := by
  have := discreteHilbertBound_pos
  unfold quarticHilbertBound
  positivity

/-- A uniform quartic estimate, independent of the finite Fourier support. -/
theorem norm_finiteHilbert_four_le (a : ℤ →₀ ℂ) :
    ‖finiteHilbertCoeffs (p := 4) (by norm_num) a‖ ≤
      quarticHilbertBound * ‖Coeff.ofFinsupp (p := 4) a‖ := by
  let x := ‖finiteHilbertCoeffs (p := 4) (by norm_num) a‖
  let y := ‖Coeff.ofFinsupp (p := 4) a‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have hM : 0 ≤ ‖hilbertSquareCoeffs‖ := norm_nonneg _
  have hB := discreteHilbertBound_pos
  have hq := finiteHilbert_quartic_quadratic a
  change x^2 ≤ 2 * discreteHilbertBound * y * x + 3 * ‖hilbertSquareCoeffs‖ * y^2 at hq
  change x ≤ quarticHilbertBound * y
  by_contra h
  have hc : quarticHilbertBound * y < x := lt_of_not_ge h
  have hC : 1 ≤ quarticHilbertBound := by unfold quarticHilbertBound; linarith
  have hxy : y ≤ x := le_trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hC) hy]) hc.le
  have hpos : 0 < x := lt_of_le_of_lt (by positivity : 0 ≤ quarticHilbertBound * y) hc
  have hstep := mul_pos (sub_pos.mpr hc) hpos
  have herr := mul_nonneg (show 0 ≤ 3 * ‖hilbertSquareCoeffs‖ * y by positivity) (sub_nonneg.mpr hxy)
  have hyx := mul_nonneg hy hx
  unfold quarticHilbertBound at hstep
  nlinarith

/-- The ordinary Hilbert transform on arbitrary quartic-summable sequences. -/
def discreteHilbertFour : Coeff 4 →L[ℂ] Coeff 4 :=
  (finiteHilbertCoeffs (p := 4) (by norm_num)).extendOfNorm Coeff.ofFinsupp

theorem discreteHilbertFour_finite_eq (a : ℤ →₀ ℂ) :
    discreteHilbertFour (Coeff.ofFinsupp a) = finiteHilbertCoeffs (p := 4) (by norm_num) a :=
  LinearMap.extendOfNorm_eq (f := finiteHilbertCoeffs (p := 4) (by norm_num))
    (e := Coeff.ofFinsupp (p := 4)) (Coeff.denseRange_ofFinsupp (p := 4) (by simp))
    ⟨quarticHilbertBound, norm_finiteHilbert_four_le⟩ a

theorem discreteHilbertFour_finite (a : ℤ →₀ ℂ) (n : ℤ) :
    discreteHilbertFour (Coeff.ofFinsupp a) n = finiteHilbert a n := by
  rw [discreteHilbertFour_finite_eq, finiteHilbertCoeffs_apply]

theorem norm_discreteHilbertFour_le : ‖discreteHilbertFour‖ ≤ quarticHilbertBound :=
  LinearMap.opNorm_extendOfNorm_le (f := finiteHilbertCoeffs (p := 4) (by norm_num))
    (e := Coeff.ofFinsupp (p := 4)) (Coeff.denseRange_ofFinsupp (p := 4) (by simp)) quarticHilbertBound_pos.le
    norm_finiteHilbert_four_le

theorem norm_discreteHilbertFour_apply_le (a : Coeff 4) :
    ‖discreteHilbertFour a‖ ≤ quarticHilbertBound * ‖a‖ :=
  discreteHilbertFour.le_of_opNorm_le norm_discreteHilbertFour_le a

/-- The shifted transform on `ℓ4`, with the same normalization as the interval coefficients. -/
def shiftedHilbertFour : Coeff 4 →L[ℂ] Coeff 4 :=
  ((Real.pi : ℂ)⁻¹) • (discreteHilbertFour - hilbertCorrectionCLM)

/-- An explicit quartic bound for the normalized shifted transform. -/
def shiftedQuarticBound : ℝ := Real.pi⁻¹ * (quarticHilbertBound + ‖hilbertCorrectionCoeffs‖)

theorem norm_shiftedHilbertFour_apply_le (a : Coeff 4) :
    ‖shiftedHilbertFour a‖ ≤ shiftedQuarticBound * ‖a‖ := by
  change ‖((Real.pi : ℂ)⁻¹) • (discreteHilbertFour a - hilbertCorrectionCLM a)‖ ≤ _
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ Real.pi⁻¹ * (‖discreteHilbertFour a‖ + ‖hilbertCorrectionCLM a‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ Real.pi⁻¹ * (quarticHilbertBound * ‖a‖ + ‖a‖ * ‖hilbertCorrectionCoeffs‖) := by
      gcongr
      · exact norm_discreteHilbertFour_apply_le a
      · exact norm_hilbertCorrectionCLM_apply_le a
    _ = _ := by unfold shiftedQuarticBound; ring

/-- The quartic extension retains exactly the original shifted reciprocal formula. -/
theorem shiftedHilbertFour_finite (a : ℤ →₀ ℂ) (n : ℤ) :
    shiftedHilbertFour (Coeff.ofFinsupp a) n =
      a.sum (fun k z => z * (2 / ((Real.pi : ℂ) * (2 * k - 2 * n - 1)))) := by
  change (Real.pi : ℂ)⁻¹ * (discreteHilbertFour (Coeff.ofFinsupp a) n -
    hilbertCorrectionCLM (Coeff.ofFinsupp (p := 4) a) n) = _
  rw [discreteHilbertFour_finite, hilbertCorrectionCLM_finite]
  have he : finiteHilbert a n = (Real.pi : ℂ) * shiftedHilbert (Coeff.ofFinsupp a) n +
      a.sum (fun k z => z * hilbertCorrection (n - k)) := by
    rw [← discreteHilbert_finite]
    change (Real.pi : ℂ) * shiftedHilbert (Coeff.ofFinsupp a) n +
      hilbertCorrectionCLM (Coeff.ofFinsupp (p := 2) a) n = _
    rw [hilbertCorrectionCLM_finite]
  rw [he, add_sub_cancel_right,
    inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), shiftedHilbert_finite]

end NLS.Fourier
