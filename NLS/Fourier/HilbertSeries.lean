import NLS.Fourier.HilbertBoundedness

/-!
# Absolutely convergent coefficient formulas for Hilbert transforms

At every `1<p<∞`, conjugate coefficient duality identifies the completed
operators with their reciprocal series on all inputs, not only finite inputs.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- A shifted, reflected single-mode image represents the shifted coefficient functional. -/
def shiftedHilbertTest (hq : 1 < q) (hqtop : q ≠ ⊤) (n : ℤ) : Coeff q :=
  Coeff.reflection (shiftedHilbertTransform hq hqtop (Coeff.ofFinsupp (Finsupp.single (-n) 1)))

theorem shiftedHilbertTest_apply (hq : 1 < q) (hqtop : q ≠ ⊤) (n k : ℤ) :
    shiftedHilbertTest hq hqtop n k = 2 / ((Real.pi : ℂ) * (2*k - 2*n - 1)) := by
  rw [shiftedHilbertTest, Coeff.reflection_apply, shiftedHilbertTransform_finite]
  simp only [Finsupp.sum_single_index, one_mul, zero_mul, Int.cast_neg]
  congr 2
  ring

/-- The ordinary test is the negative of a single-mode Hilbert image. -/
def ordinaryHilbertTest (hq : 1 < q) (hqtop : q ≠ ⊤) (n : ℤ) : Coeff q :=
  -hilbertTransform hq hqtop (Coeff.ofFinsupp (Finsupp.single n 1))

theorem ordinaryHilbertTest_apply (hq : 1 < q) (hqtop : q ≠ ⊤) (n k : ℤ) :
    ordinaryHilbertTest hq hqtop n k = ((k : ℂ)-n)⁻¹ := by
  change -hilbertTransform hq hqtop (Coeff.ofFinsupp (Finsupp.single n 1)) k = _
  rw [hilbertTransform_finite]
  simp only [finiteHilbert, Finsupp.sum_single_index, zero_div, one_div]
  rw [show (n : ℂ)-k = -((k : ℂ)-n) by ring, inv_neg, neg_neg]

/-- The ordinary reciprocal series is absolutely convergent on every input. -/
theorem summable_norm_hilbertSeries (hq : 1 < q) (hqtop : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k / ((k : ℂ)-n)‖) := by
  simpa only [ordinaryHilbertTest_apply, div_eq_mul_inv] using
    Coeff.summable_norm_dualPairing a (ordinaryHilbertTest hq hqtop n)

/-- The shifted reciprocal series is absolutely convergent on every input. -/
theorem summable_norm_shiftedHilbertSeries (hq : 1 < q) (hqtop : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k * (2 / ((Real.pi : ℂ) * (2*k - 2*n - 1)))‖) := by
  simpa only [shiftedHilbertTest_apply] using
    Coeff.summable_norm_dualPairing a (shiftedHilbertTest hq hqtop n)

/-- The completed ordinary transform has the source series on all inputs. -/
theorem hilbertTransform_apply (hp : 1 < p) (hptop : p ≠ ⊤)
    (hq : 1 < q) (hqtop : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    hilbertTransform hp hptop a n = ∑' k : ℤ, a k / ((k : ℂ)-n) := by
  have he : hilbertTransform hp hptop a n = Coeff.dualPairing a (ordinaryHilbertTest hq hqtop n) := by
    refine Dense.induction (Coeff.denseRange_ofFinsupp hptop) ?_ ?_ a
    · rintro _ ⟨b, rfl⟩
      rw [hilbertTransform_finite, Coeff.dualPairing_finite_left]
      simp only [ordinaryHilbertTest_apply, finiteHilbert, div_eq_mul_inv]
    · exact isClosed_eq ((lp.evalCLM ℂ _ _ n).continuous.comp (hilbertTransform hp hptop).continuous)
        (Coeff.dualPairing.flip (ordinaryHilbertTest hq hqtop n)).continuous
  rw [he, Coeff.dualPairing_apply]
  simp only [ordinaryHilbertTest_apply, div_eq_mul_inv]

/-- The completed shifted transform has the normalized reciprocal series on all inputs. -/
theorem shiftedHilbertTransform_apply (hp : 1 < p) (hptop : p ≠ ⊤)
    (hq : 1 < q) (hqtop : q ≠ ⊤) (a : Coeff p) (n : ℤ) :
    shiftedHilbertTransform hp hptop a n =
      ∑' k : ℤ, a k * (2 / ((Real.pi : ℂ) * (2*k - 2*n - 1))) := by
  have he : shiftedHilbertTransform hp hptop a n =
      Coeff.dualPairing a (shiftedHilbertTest hq hqtop n) := by
    refine Dense.induction (Coeff.denseRange_ofFinsupp hptop) ?_ ?_ a
    · rintro _ ⟨b, rfl⟩
      rw [shiftedHilbertTransform_finite, Coeff.dualPairing_finite_left]
      simp only [shiftedHilbertTest_apply]
    · exact isClosed_eq ((lp.evalCLM ℂ _ _ n).continuous.comp (shiftedHilbertTransform hp hptop).continuous)
        (Coeff.dualPairing.flip (shiftedHilbertTest hq hqtop n)).continuous
  rw [he, Coeff.dualPairing_apply]
  simp only [shiftedHilbertTest_apply]

end NLS.Fourier
