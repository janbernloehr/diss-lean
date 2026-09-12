import NLS.Fourier.HilbertEstimate
import NLS.SequenceSpaces.ConjugateDuality

/-!
# Hilbert estimates at conjugate exponents

The ordinary discrete Hilbert kernel is antisymmetric, including its zero
diagonal. Transposition on finite sequences and norm detection by finite
conjugate tests transfer a proved bound without increasing its constant.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier

/-- Transposition reverses the sign of the finite discrete Hilbert transform. -/
theorem finiteHilbert_transpose (a b : ℤ →₀ ℂ) :
    b.sum (fun n z => finiteHilbert a n * z) =
      -a.sum (fun n z => finiteHilbert b n * z) := by
  classical
  simp only [finiteHilbert, Finsupp.sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro n hn
  rw [show (n : ℂ) - k = -((k : ℂ) - n) by ring, div_neg]
  ring

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- The finite Hilbert estimate transfers to a conjugate exponent with the same constant. -/
theorem norm_finiteHilbert_conjugate_le (h : HilbertEstimate q) (hp : 1 < p) (hptop : p ≠ ⊤)
    (a : ℤ →₀ ℂ) :
    ‖finiteHilbertCoeffs hp a‖ ≤ h.bound * ‖Coeff.ofFinsupp (p := p) a‖ := by
  have hpReal : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp).ne' hptop
  have hqReal : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans h.one_lt).ne' h.ne_top
  apply Coeff.norm_le_of_finite_dual (q := q) hpReal hqReal hptop _ (mul_nonneg h.bound_nonneg (norm_nonneg _))
  intro b
  simp only [finiteHilbertCoeffs_apply]
  rw [finiteHilbert_transpose, norm_neg]
  have he : a.sum (fun n z => finiteHilbert b n * z) =
      Coeff.dualPairing (Coeff.ofFinsupp (p := p) a) (h.operator (Coeff.ofFinsupp b)) := by
    rw [Coeff.dualPairing_finite_left]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only
    rw [h.operator_finite, mul_comm]
  rw [he]
  calc
    _ ≤ ‖Coeff.ofFinsupp (p := p) a‖ * ‖h.operator (Coeff.ofFinsupp b)‖ :=
      Coeff.norm_dualPairing_le _ _
    _ ≤ ‖Coeff.ofFinsupp (p := p) a‖ * (h.bound * ‖Coeff.ofFinsupp (p := q) b‖) :=
      mul_le_mul_of_nonneg_left (h.norm_operator_apply_le _) (norm_nonneg _)
    _ = _ := by ring

/-- Package the transferred bound, so it supplies completed ordinary and shifted operators. -/
def HilbertEstimate.conjugateTo (h : HilbertEstimate q) (hp : 1 < p) (hptop : p ≠ ⊤) :
    HilbertEstimate p where
  one_lt := hp
  ne_top := hptop
  bound := h.bound
  bound_nonneg := h.bound_nonneg
  finite_bound := norm_finiteHilbert_conjugate_le h hp hptop

/-- Completed transforms retain the transposition identity on all conjugate inputs. -/
theorem HilbertEstimate.dualPairing_operator (hp : HilbertEstimate p) (hq : HilbertEstimate q)
    (a : Coeff p) (b : Coeff q) :
    Coeff.dualPairing (hp.operator a) b = -Coeff.dualPairing a (hq.operator b) := by
  let P := Coeff.dualPairing (p := p) (q := q)
  have he : (P.comp hp.operator) = -((hq.operator.precomp ℂ).comp P) := by
    apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    change P (hp.operator x) y = -P x (hq.operator y)
    refine Dense.induction (Coeff.denseRange_ofFinsupp hp.ne_top) ?_ ?_ x
    · rintro _ ⟨a, rfl⟩
      refine Dense.induction (Coeff.denseRange_ofFinsupp hq.ne_top) ?_ ?_ y
      · rintro _ ⟨b, rfl⟩
        simp only [P, Coeff.dualPairing_finite_right, Coeff.dualPairing_finite_left,
          hp.operator_finite, hq.operator_finite]
        rw [finiteHilbert_transpose]
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        exact mul_comm _ _
      · exact isClosed_eq (P (hp.operator (Coeff.ofFinsupp a))).continuous
          ((P (Coeff.ofFinsupp a)).continuous.comp hq.operator.continuous).neg
    · exact isClosed_eq ((P.flip y).continuous.comp hp.operator.continuous)
        (P.flip (hq.operator y)).continuous.neg
  exact congrArg (fun T : Coeff p →L[ℂ] Coeff q →L[ℂ] ℂ => T a b) he

end NLS.Fourier
