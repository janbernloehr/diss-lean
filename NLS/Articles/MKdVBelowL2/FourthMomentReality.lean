import NLS.Articles.MKdVBelowL2.FourthMomentAnalytic
import NLS.ZakharovShabat.SourceMomentReality

/-! # Reality of the weighted fourth-frequency moments

The even-moment reality theorem applies before summation, so the literal
weighted H₄ sum is real at every real source, including collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex ComplexConjugate
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual weighted second-moment sum has real values on the real form. -/
theorem fourthFrequencyCandidate_im_eq_zero
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (fourthFrequencyCandidate A n φ.val).im = 0 := by
  have hm (k : ℤ) : conj (A.moment n k 2 φ.val) = A.moment n k 2 φ.val :=
    Complex.conj_eq_iff_im.mpr (A.positive_even_moment_im_eq_zero hs φ n k 0)
  apply Complex.conj_eq_iff_im.mp
  simp [fourthFrequencyCandidate,Complex.conj_tsum,Complex.conj_ofNat,hm]

end NLS.Articles.MKdVBelowL2
