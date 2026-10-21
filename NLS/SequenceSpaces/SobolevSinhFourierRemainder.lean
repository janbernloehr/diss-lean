import NLS.SequenceSpaces.SobolevSinhLinearization
import NLS.SequenceSpaces.SobolevDerivative

/-! # Transferring a sine Fourier remainder to its phase

A sharper Fourier remainder for the hyperbolic sine transfers to the small phase itself with an explicit weighted norm bound.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A one-order smoother Fourier remainder for the hyperbolic sine of
a small inverse-index phase gives the same remainder for the phase itself. -/
theorem exists_sobolev_sinh_fourier_remainder
    (r : ℝ) (u : ℤ → ℂ) (a : WeightedCoeff (Weight.sobolev r) p)
    (e : WeightedCoeff (Weight.sobolev (r+1)) p) (D : ℝ) (hD : 0 ≤ D)
    (he : ∀ n, e.val n = sinh (u n)-a.val n)
    (hu : ∀ n, ‖u n‖ ≤ 1)
    (hsmall : ∀ n, ‖u n‖ ≤ 2*‖sinh (u n)‖)
    (hdecay : ∀ n : ℤ, (1+|(n:ℝ)|)*‖u n‖ ≤ D) :
    ∃ f : WeightedCoeff (Weight.sobolev (r+1)) p,
      (∀ n, f.val n = u n-a.val n) ∧
      ‖f‖ ≤ (2*D)*(‖e‖+‖a‖)+‖e‖ := by
  let b : WeightedCoeff (Weight.sobolev r) p := sobolevInclusion (by linarith : r ≤ r+1) e+a
  have hb (n : ℤ) : b.val n = sinh (u n) := by
    simp only [b,add_val,sobolevInclusion_apply,he,sub_add_cancel]
  have hbn : ‖b‖ ≤ ‖e‖+‖a‖ := (norm_add_le _ _).trans
    (add_le_add (norm_sobolevInclusion_le _ e) le_rfl)
  obtain ⟨_,f,_,hf,_,hfn⟩ := exists_sobolev_sinh_linearization r u b D hD hb hu
    (fun n => by simpa only [hb] using hsmall n) hdecay
  refine ⟨f+e,?_,?_⟩
  · intro n
    rw [add_val,hf n,hb n,he n]
    ring
  · exact (norm_add_le _ _).trans ((add_le_add
      (hfn.trans (mul_le_mul_of_nonneg_left hbn (by positivity))) le_rfl))

end NLS.WeightedCoeff
