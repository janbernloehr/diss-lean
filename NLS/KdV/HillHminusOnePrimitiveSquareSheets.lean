import NLS.KdV.HillHminusOnePrimitiveSheets
import NLS.KdV.HillHminusOneJointGapRoots
import NLS.ComplexAnalysis.PrincipalSquareRootSheet

/-! # Exact physical sheets of the actual filled high Hill square

The global physical sign fixes the square-root sign of every actual
shifted primitive. The result applies to the same squares used in the
intrinsic joint normalization, on both nonreal halves of every disc.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusShiftedPrimitive_eq_principalSqrt
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) (z v : ℂ)
    (hz : 0 < z.im)
    (hsq : (hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^2 = v) :
    hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi = Complex.sqrt v := by
  apply eq_principalSqrt_of_sq_of_re_pos _ v hsq
  simpa using hillHminusContinuedPrimitive_re_pos q hq z hz

theorem hillHminusShiftedPrimitive_eq_neg_principalSqrt
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (n : ℕ+) (z v : ℂ)
    (hz : z.im < 0)
    (hsq : (hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^2 = v) :
    hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi = -Complex.sqrt v := by
  apply eq_neg_principalSqrt_of_sq_of_re_neg _ v hsq
  simpa using hillHminusContinuedPrimitive_re_neg q hq z hz

/-- The actual filled-square identity determines BOTH physical half-plane
sheets, for every real input in the original complex potential neighborhood. -/
theorem hillHminus_whole_disc_square_physical_sheets
    (n : ℕ+) (r : ℝ) (V : Set PeriodOneHminusOne)
    (K : ℂ × PeriodOneHminusOne → ℂ)
    (hmatch : ∀ t ∈ (hillHminusGapSquareDisc n r ×ˢ V) ∩ hillHminusContinuationDomain,
      K t = (hillHminusContinuedPrimitive t+I*(n : ℂ)*Real.pi)^2)
    (q : PeriodOneHminusOne) (hqV : q ∈ V) (hq : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z ∈ hillHminusGapSquareDisc n r) (him : z.im ≠ 0) :
    hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi =
      if 0 < z.im then Complex.sqrt (K (z,q)) else -Complex.sqrt (K (z,q)) := by
  have hs := (hmatch (z,q) ⟨⟨hz,hqV⟩,
    mem_hillHminusContinuationDomain_of_im_ne_zero q hq z him⟩).symm
  by_cases hup : 0 < z.im
  · rw [if_pos hup]
    exact hillHminusShiftedPrimitive_eq_principalSqrt q hq n z _ hup hs
  · rw [if_neg hup]
    exact hillHminusShiftedPrimitive_eq_neg_principalSqrt q hq n z _
      (lt_of_le_of_ne (not_lt.mp hup) him) hs

end NLS.KdV
