import NLS.ZakharovShabat.DiscriminantPairFactorization
import NLS.ZakharovShabat.CanonicalPeriodicFree
import NLS.ZakharovShabat.FreeSineQuotient

/-!
# Free normalization of the remaining periodic product

At zero potential, removing the nth doubled root leaves the square of the
filled sine quotient. Its value at the removed root is one. In particular,
the corrected negative factorization extends across every collapsed free gap.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp] theorem canonicalPeriodicMidpoint_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    canonicalPeriodicMidpoint hp hp1 0 (pairParitySubspace 0).zero_mem n = (Real.pi : ℂ)*n := by
  simp only [canonicalPeriodicMidpoint,canonicalPeriodicLeft_zero,canonicalPeriodicRight_zero]
  ring

@[simp] theorem canonicalPeriodicGap_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    canonicalPeriodicGap hp hp1 0 (pairParitySubspace 0).zero_mem n = 0 := by
  simp only [canonicalPeriodicGap,canonicalPeriodicLeft_zero,canonicalPeriodicRight_zero,sub_self]

/-- The filled squared sine quotient is the remaining free product at every spectral point. -/
theorem canonicalDeletedPeriodicProduct_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    canonicalDeletedPeriodicProduct hp hp1 0 (pairParitySubspace 0).zero_mem n =
      fun z => (freeSineQuotient n z)^2 := by
  apply Continuous.ext_on ((Set.to_countable {(Real.pi : ℂ)*n}).dense_compl ℂ)
    (continuousOn_univ.mp (analyticOnNhd_canonicalDeletedPeriodicProduct hp hp1 0
      (pairParitySubspace 0).zero_mem n).continuousOn) ((continuous_freeSineQuotient n).pow 2)
  intro z hz
  change canonicalDeletedPeriodicProduct hp hp1 0 (pairParitySubspace 0).zero_mem n z = (freeSineQuotient n z)^2
  have hz' : z ≠ (Real.pi : ℂ)*n := by simpa using hz
  have he := canonicalDiscriminant_sq_sub_four_eq_midpoint_mul hp hp1 0
    (pairParitySubspace 0).zero_mem n z
  simp only [canonicalDiscriminant_zero_finite,canonicalPeriodicMidpoint_zero,canonicalPeriodicGap_zero,
    zero_pow (by decide : 2 ≠ 0),zero_div,sub_zero] at he
  have hfree : (freeDiscriminant z)^2-4 = -4*sin z^2 := by
    have hs := sin_sq_add_cos_sq z
    unfold freeDiscriminant
    linear_combination 4*hs
  rw [hfree,← freeSineQuotient_mul_sub n z] at he
  apply mul_left_cancel₀ (show -4*(z-(Real.pi : ℂ)*n)^2 ≠ 0 from
    mul_ne_zero (by norm_num) (pow_ne_zero _ (sub_ne_zero.mpr hz')))
  linear_combination -he

/-- The free remaining product has unit value even at its removed double root. -/
@[simp] theorem canonicalDeletedPeriodicProduct_zero_center (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    canonicalDeletedPeriodicProduct hp hp1 0 (pairParitySubspace 0).zero_mem n ((Real.pi : ℂ)*n) = 1 := by
  rw [canonicalDeletedPeriodicProduct_zero]
  dsimp only
  rw [freeSineQuotient_center]
  have hs := sin_sq_add_cos_sq ((Real.pi : ℂ)*n)
  have hz : sin ((Real.pi : ℂ)*n) = 0 := by simpa [mul_comm] using sin_int_mul_pi n
  simpa only [hz,zero_pow (by decide : 2 ≠ 0),zero_add] using hs

end NLS.ZakharovShabat
