import NLS.Fourier.HilbertEstimate
import NLS.SequenceSpaces.DoublingProduct

/-!
# Exponent doubling for the discrete Hilbert transform

The finite Cotlar identity and Hölder turn any proved estimate at `p` into
an estimate at `q=2p`. All constants are uniform over finite supports, and
`HilbertEstimate` then supplies the unique continuous completion.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Fourier
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderTriple q p]

/-- Cotlar's quadratic estimate at general doubled exponents. -/
theorem finiteHilbert_doubling_quadratic (h : HilbertEstimate p) (hq : 1 < q)
    (hreal : q.toReal = 2 * p.toReal) (a : ℤ →₀ ℂ) :
    ‖finiteHilbertCoeffs hq a‖^2 ≤
      2 * h.bound * ‖Coeff.ofFinsupp (p := q) a‖ * ‖finiteHilbertCoeffs hq a‖ +
      3 * ‖hilbertSquareCoeffs‖ * ‖Coeff.ofFinsupp (p := q) a‖^2 := by
  have hpReal : 0 < p.toReal := ENNReal.toReal_pos
    (zero_lt_one.trans h.one_lt).ne' h.ne_top
  let u : Coeff q := Coeff.ofFinsupp a
  let v : Coeff q := finiteHilbertCoeffs hq a
  let w : Coeff p := Coeff.ofFinsupp (finiteProduct a (finiteHilbert a))
  let s : Coeff p := Coeff.ofFinsupp (finiteProduct a a)
  have hw : w = (Coeff.doublingProduct (p := p)) u v := by
    apply lp.ext
    funext n
    simp only [w, u, v, Coeff.ofFinsupp_apply, finiteProduct_apply,
      Coeff.doublingProduct_apply, finiteHilbertCoeffs_apply]
  have hs : s = (Coeff.doublingProduct (p := p)) u u := by
    apply lp.ext
    funext n
    rfl
  have he : (Coeff.doublingProduct (p := p)) v v =
      (2 : ℂ) • h.operator w + hilbertSquare s +
        (2 : ℂ) • (Coeff.doublingProduct (p := p)) u (hilbertSquare u) := by
    apply lp.ext
    funext n
    change v n * v n = 2 * h.operator w n + hilbertSquare s n +
      2 * (u n * hilbertSquare u n)
    simp only [u, v, w, s, finiteHilbertCoeffs_apply, h.operator_finite,
      hilbertSquare_finite, Coeff.ofFinsupp_apply]
    simpa only [pow_two, mul_assoc] using finiteHilbert_cotlar a n
  have hwbound : ‖w‖ ≤ ‖u‖ * ‖v‖ := by rw [hw]; exact Coeff.norm_doublingProduct_le (p := p) u v
  have hsbound : ‖s‖ = ‖u‖^2 := by rw [hs, Coeff.norm_doublingProduct_self hpReal hreal]
  have hH : ‖h.operator w‖ ≤ h.bound * (‖u‖ * ‖v‖) :=
    (h.norm_operator_apply_le w).trans
      (mul_le_mul_of_nonneg_left hwbound h.bound_nonneg)
  have hR : ‖hilbertSquare s‖ ≤ ‖u‖^2 * ‖hilbertSquareCoeffs‖ := by
    simpa only [hsbound] using norm_hilbertSquare_apply_le s
  have hP : ‖(Coeff.doublingProduct (p := p)) u (hilbertSquare u)‖ ≤ ‖u‖ * (‖u‖ * ‖hilbertSquareCoeffs‖) :=
    (Coeff.norm_doublingProduct_le (p := p) _ _).trans
      (mul_le_mul_of_nonneg_left (norm_hilbertSquare_apply_le u) (norm_nonneg u))
  change ‖v‖^2 ≤ 2 * h.bound * ‖u‖ * ‖v‖ + 3 * ‖hilbertSquareCoeffs‖ * ‖u‖^2
  calc
    _ = ‖(Coeff.doublingProduct (p := p)) v v‖ := (Coeff.norm_doublingProduct_self hpReal hreal v).symm
    _ = ‖(2 : ℂ) • h.operator w + hilbertSquare s +
        (2 : ℂ) • (Coeff.doublingProduct (p := p)) u (hilbertSquare u)‖ := by rw [he]
    _ ≤ ‖(2 : ℂ) • h.operator w‖ + ‖hilbertSquare s‖ +
        ‖(2 : ℂ) • (Coeff.doublingProduct (p := p)) u (hilbertSquare u)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = 2 * ‖h.operator w‖ + ‖hilbertSquare s‖ +
        2 * ‖(Coeff.doublingProduct (p := p)) u (hilbertSquare u)‖ := by simp only [norm_smul]; norm_num
    _ ≤ 2 * (h.bound * (‖u‖ * ‖v‖)) + ‖u‖^2 * ‖hilbertSquareCoeffs‖ +
        2 * (‖u‖ * (‖u‖ * ‖hilbertSquareCoeffs‖)) := by gcongr
    _ = _ := by ring

/-- Solving the quadratic bound requires no choice of roots or positive-input division. -/
theorem cotlar_quadratic_bound {x y B M : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hq : x^2 ≤ 2 * B * y * x + 3 * M * y^2) :
    x ≤ (2 * B + 3 * M + 1) * y := by
  by_contra h
  have hc : (2 * B + 3 * M + 1) * y < x := lt_of_not_ge h
  have hC : 1 ≤ 2 * B + 3 * M + 1 := by linarith
  have hxy : y ≤ x := le_trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hC) hy]) hc.le
  have hpos : 0 < x := lt_of_le_of_lt (by positivity : 0 ≤ (2 * B + 3 * M + 1) * y) hc
  have hstep := mul_pos (sub_pos.mpr hc) hpos
  have herr := mul_nonneg (show 0 ≤ 3 * M * y by positivity) (sub_nonneg.mpr hxy)
  have hyx := mul_nonneg hy hx
  nlinarith

/-- The recurrence for the uniform Hilbert bound after one exponent doubling. -/
def doubledHilbertBound (B : ℝ) : ℝ := 2 * B + 3 * ‖hilbertSquareCoeffs‖ + 1

theorem doubledHilbertBound_pos {B : ℝ} (hB : 0 ≤ B) : 0 < doubledHilbertBound B := by
  unfold doubledHilbertBound
  positivity

/-- One exponent-doubling step yields a uniform bound on every finite input. -/
theorem norm_finiteHilbert_double_le (h : HilbertEstimate p) (hq : 1 < q)
    (hreal : q.toReal = 2 * p.toReal) (a : ℤ →₀ ℂ) :
    ‖finiteHilbertCoeffs hq a‖ ≤ doubledHilbertBound h.bound * ‖Coeff.ofFinsupp (p := q) a‖ :=
  cotlar_quadratic_bound (norm_nonneg _) (norm_nonneg _) h.bound_nonneg
    (norm_nonneg _) (finiteHilbert_doubling_quadratic h hq hreal a)

/-- Package the new proved estimate so it can be iterated and completed. -/
def HilbertEstimate.doubleTo (h : HilbertEstimate p) (hq : 1 < q) (hqtop : q ≠ ⊤)
    (hreal : q.toReal = 2 * p.toReal) : HilbertEstimate q where
  one_lt := hq
  ne_top := hqtop
  bound := doubledHilbertBound h.bound
  bound_nonneg := (doubledHilbertBound_pos h.bound_nonneg).le
  finite_bound := norm_finiteHilbert_double_le h hq hreal

end NLS.Fourier
