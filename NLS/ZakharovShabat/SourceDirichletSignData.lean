import NLS.ZakharovShabat.SourceIsospectralSet
import NLS.ZakharovShabat.SourceAntiDiscriminantIdentity
import NLS.ZakharovShabat.RealGapProductSigns
import Mathlib.Data.Sign.Basic

/-! # The actual signed Dirichlet terminal data

At every real source and every index, the terminal anti-discriminant is
real, including at periodic endpoints. On an actual isospectral set, its
square is fixed by the Dirichlet eigenvalue. Consequently the eigenvalue
and the sign recover the full terminal sheet value. This is only the
scalar recovery step, not an inverse spectral uniqueness theorem.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual anti-discriminant at a real source's Dirichlet eigenvalue is real. -/
theorem sourceDirichletTerminalAntiDiscriminant_im_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (sourceAntiDiscriminantCandidate hp hp1 φ.val
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n)).im = 0 := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n
  let Δ := canonicalDiscriminant hp (periodOnePotential φ.val) μ
  let S := sourceAntiDiscriminantCandidate hp hp1 φ.val μ
  have hμ : (μ.re : ℂ) = μ := Complex.ext rfl (by
    simpa only [ofReal_im] using
      (canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 .dirichlet φ.val φ.property n).symm)
  have hreal := isRealType_periodOnePotential φ.val φ.property
  have hΔ : Δ.im = 0 := by
    change (canonicalDiscriminant hp (periodOnePotential φ.val) μ).im = 0
    rw [← hμ]
    exact canonicalDiscriminant_im_eq_zero_of_realType hp hp1 _ (periodOnePotential_mem _) hreal μ.re
  have hge : 4 ≤ Δ.re ^ 2 := by
    have hb := discriminant_re_sq_ge_four_of_mem_canonicalGap hp hp1 _
      (periodOnePotential_mem φ.val) hreal n μ.re
      (canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 .dirichlet φ.val φ.property n)
    simpa only [hμ] using hb
  have hs : Δ^2-4 = S^2 := sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 φ.val n
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  simp only [pow_two,mul_re,sub_re,hΔ,mul_zero,sub_zero,show (4 : ℂ).re = 4 from rfl] at hr
  simp only [pow_two,mul_im,sub_im,hΔ,mul_zero,zero_mul,zero_add,
    show (4 : ℂ).im = 0 from rfl,sub_zero] at hi
  change S.im = 0
  by_cases hx : S.re = 0
  · nlinarith [sq_nonneg S.im]
  · have hprod : S.re*S.im = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_left hx

/-- The sign attached to the actual Dirichlet eigenvalue; zero at a periodic terminal. -/
def sourceDirichletSign (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) : SignType :=
  SignType.sign (sourceAntiDiscriminantCandidate hp hp1 φ.val
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n)).re

/-- On a fixed actual periodic spectrum, equal Dirichlet eigenvalues and signs
recover equality of the full anti-discriminant, including its zero value. -/
theorem sourceDirichletTerminal_eq_of_isospectral_root_sign
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val n =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n)
    (hσ : sourceDirichletSign hp hp1 ψ n = sourceDirichletSign hp hp1 φ n) :
    sourceAntiDiscriminantCandidate hp hp1 ψ.val
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val n) =
    sourceAntiDiscriminantCandidate hp hp1 φ.val
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n) := by
  let A := sourceAntiDiscriminantCandidate hp hp1 ψ.val
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val n)
  let B := sourceAntiDiscriminantCandidate hp hp1 φ.val
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n)
  have hΔ := (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mp h
  have hs : A^2 = B^2 := by
    rw [← sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 ψ.val n,
      ← sourceDiscriminant_sq_sub_four_at_canonicalDirichletRoot hp hp1 φ.val n,hΔ,hμ]
  have ha : |A.re| = |B.re| := by
    rcases eq_or_eq_neg_of_sq_eq_sq A B hs with he | he
    · rw [he]
    · rw [he,neg_re,abs_neg]
  have hsign : SignType.sign A.re = SignType.sign B.re := hσ
  apply Complex.ext
  · calc
      A.re = SignType.sign A.re * |A.re| := (sign_mul_abs _).symm
      _ = SignType.sign B.re * |B.re| := by rw [hsign,ha]
      _ = B.re := sign_mul_abs _
  · exact (sourceDirichletTerminalAntiDiscriminant_im_eq_zero hp hp1 ψ n).trans
      (sourceDirichletTerminalAntiDiscriminant_im_eq_zero hp hp1 φ n).symm

end NLS.ZakharovShabat
