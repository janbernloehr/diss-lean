import NLS.ZakharovShabat.SourceCanonicalRootUpperParitySign
import NLS.ZakharovShabat.SourceActionZeroGapPositive

/-!
# Derivative parity on real source gaps

The real half-discriminant incorporates the gap-index parity sign.
The complex discriminant derivative consequently has the same sign
as the upper canonical-root boundary value.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complex discriminant derivative is twice the signed real
half-discriminant derivative, with explicit absolute-index parity. -/
theorem discriminant_derivative_eq_signed_two_realGapHalfDiscriminant_deriv
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (x : ℝ) :
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (x:ℂ) =
      (((-1:ℝ)^n.natAbs *
        (2*deriv (realGapHalfDiscriminant hp
          (periodOnePotential ψ) n) x):ℝ):ℂ) := by
  let φ := periodOnePotential ψ
  let D : ℝ → ℝ := fun y => (canonicalDiscriminant hp φ (y:ℂ)).re
  have hdiff : Differentiable ℂ (canonicalDiscriminant hp φ) :=
    fun z => (analyticOnNhd_canonicalDiscriminant hp hp1 φ
      (periodOnePotential_mem ψ) z (mem_univ _)).differentiableAt
  have hDderiv : deriv D x =
      (deriv (canonicalDiscriminant hp φ) (x:ℂ)).re :=
    NLS.ComplexAnalysis.deriv_real_axis_re _ hdiff x
  have him := discriminant_derivative_im_eq_zero_of_realType
    hp hp1 φ (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) x
  have hcast : ((deriv (canonicalDiscriminant hp φ) (x:ℂ)).re:ℂ) =
      deriv (canonicalDiscriminant hp φ) (x:ℂ) := by
    apply Complex.ext
    · rfl
    · exact him.symm
  by_cases hn : n % 2 = 0
  · have hEven : Even n := Int.even_iff.mpr hn
    have hs : (-1:ℝ)^n.natAbs = 1 :=
      Even.neg_one_pow (Int.natAbs_even.mpr hEven)
    have hg : realGapHalfDiscriminant hp φ n =
        fun y : ℝ => D y/2 := by
      funext y
      simp [realGapHalfDiscriminant,D,hn]
    have hgderiv : deriv (realGapHalfDiscriminant hp φ n) x =
        deriv D x/2 := by rw [hg,deriv_div_const]
    rw [← hcast]
    congr 1
    rw [hs,hgderiv,hDderiv]
    ring
  · have hOdd : Odd n := Int.not_even_iff_odd.mp
      (fun he => hn (Int.even_iff.mp he))
    have hs : (-1:ℝ)^n.natAbs = -1 :=
      Odd.neg_one_pow (Int.natAbs_odd.mpr hOdd)
    have hg : realGapHalfDiscriminant hp φ n =
        fun y : ℝ => -D y/2 := by
      funext y
      simp [realGapHalfDiscriminant,D,hn]
    have hgderiv : deriv (realGapHalfDiscriminant hp φ n) x =
        -deriv D x/2 := by
      rw [hg,deriv_div_const]
      change deriv (-D) x / 2 = -deriv D x / 2
      rw [deriv.neg]
    rw [← hcast]
    congr 1
    rw [hs,hgderiv,hDderiv]
    ring

end NLS.ZakharovShabat
