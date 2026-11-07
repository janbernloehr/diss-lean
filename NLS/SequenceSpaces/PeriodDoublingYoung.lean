import NLS.SequenceSpaces.PeriodDoubling
import NLS.SequenceSpaces.YoungConvolution

/-! Physical period doubling preserves every actual Young convolution. -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

theorem periodDouble_youngConvolution (h : YoungRelation p q r) (a : Coeff p) (b : Coeff q) :
    periodDouble (youngConvolution h a b) = youngConvolution h (periodDouble a) (periodDouble b) := by
  ext n
  by_cases hn : n % 2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he,periodDouble_even,youngConvolution_apply,youngConvolution_apply]
    have hs := (parityEmbedding 0).injective.tsum_eq
      (f := fun j : ℤ => periodDouble a (2*(n/2)-j)*periodDouble b j) (by
        intro j hj
        by_contra hout
        have hz := insert_apply_outside (parityEmbedding 0) b j hout
        exact hj (by change _*insert (parityEmbedding 0) b j = 0; rw [hz,mul_zero]))
    rw [← hs]
    apply tsum_congr
    intro j
    simp only [parityEmbedding_apply,add_zero]
    rw [show 2*(n/2)-2*j = 2*(n/2-j) by ring,periodDouble_even,periodDouble_even]
  · have he : n = 2*(n/2)+1 := by omega
    rw [he,periodDouble_odd,youngConvolution_apply]
    symm
    suffices hz : ∀ j : ℤ, periodDouble a (2*(n/2)+1-j)*periodDouble b j = 0 by
      simp only [hz,tsum_zero]
    intro j
    by_cases hj : j % 2 = 0
    · have hj' : j = 2*(j/2) := by omega
      rw [hj',show 2*(n/2)+1-2*(j/2) = 2*(n/2-j/2)+1 by omega,periodDouble_odd,zero_mul]
    · have hj' : j = 2*(j/2)+1 := by omega
      rw [hj',periodDouble_odd,mul_zero]

end NLS.Coeff
