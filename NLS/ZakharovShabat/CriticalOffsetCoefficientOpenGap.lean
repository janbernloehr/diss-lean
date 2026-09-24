import NLS.ZakharovShabat.CriticalMidpointGapSquared
import NLS.ZakharovShabat.CanonicalCriticalInterlacing
import NLS.ZakharovShabat.RealGapCharacterization

/-!
# Nonvanishing of the critical midpoint coefficient at open real gaps

At an open real periodic gap, the critical point lies strictly between
the endpoints. The discriminant therefore has modulus greater than
two, forcing the remaining periodic product to be nonzero there.
The exact quadratic critical-point identity then shows that the
coefficient in the squared-gap offset formula is nonzero.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A nonzero gap and nonzero remaining product force the coefficient
of the critical-to-midpoint offset to be nonzero. -/
theorem canonicalCriticalOffsetCoefficient_ne_zero_of_gap_and_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 φ heven n ≠ 0)
    (hprod : canonicalDeletedPeriodicProduct hp hp1 φ heven n
      (canonicalCriticalPoints hp hp1 φ heven n) ≠ 0) :
    canonicalCriticalOffsetCoefficient hp hp1 φ heven n ≠ 0 := by
  intro hcoeff
  have hident := canonicalCriticalOffsetCoefficient_identity hp hp1 φ heven n
  rw [hcoeff, zero_mul] at hident
  have hderiv : canonicalDeletedCriticalDerivative hp hp1 φ heven n = 0 := by
    have hpow : (canonicalPeriodicGap hp hp1 φ heven n)^2 ≠ 0 := pow_ne_zero 2 hgap
    exact ((div_eq_zero_iff).mp
      ((mul_eq_zero.mp hident.symm).resolve_left hpow)).resolve_right (by norm_num)
  have hzero : 2*canonicalDeletedPeriodicProduct hp hp1 φ heven n
      (canonicalCriticalPoints hp hp1 φ heven n) = 0 := by
    simpa [canonicalCriticalOffsetCoefficient, hderiv] using hcoeff
  exact hprod ((mul_eq_zero.mp hzero).resolve_left (by norm_num))

/-- The remaining periodic product cannot vanish at the indexed
critical point of an open real gap. -/
theorem canonicalDeletedPeriodicProduct_ne_zero_at_open_gap_critical
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ)
    (hlt : (canonicalPeriodicLeft hp hp1 φ heven n).re <
      (canonicalPeriodicRight hp hp1 φ heven n).re) :
    canonicalDeletedPeriodicProduct hp hp1 φ heven n
      (canonicalCriticalPoints hp hp1 φ heven n) ≠ 0 := by
  let c := canonicalCriticalPoints hp hp1 φ heven n
  have hinside := canonicalCriticalPoints_between_of_open_gap hp hp1 φ heven hreal n hlt
  have hrealc : (c.re : ℂ) = c := by
    apply Complex.ext <;> simp [c, canonicalCriticalPoints_im_eq_zero hp hp1 φ heven hreal n]
  have hlarge : 2 < ‖canonicalDiscriminant hp φ c‖ := by
    rw [← hrealc]
    exact two_lt_norm_discriminant_of_mem_canonicalGap_interior
      hp hp1 φ heven hreal n c.re hinside
  intro hprod
  have hfactor := canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 φ heven n c
  rw [hprod, mul_zero] at hfactor
  have hnormsq : ‖canonicalDiscriminant hp φ c‖^2 = 4 := by
    have hs : (canonicalDiscriminant hp φ c)^2 = 4 := sub_eq_zero.mp hfactor
    have hn := congrArg norm hs
    simpa only [norm_pow, Complex.norm_ofNat] using hn
  nlinarith [norm_nonneg (canonicalDiscriminant hp φ c)]

/-- The critical midpoint coefficient is nonzero at every open real
periodic gap, including the central indices. -/
theorem canonicalCriticalOffsetCoefficient_ne_zero_of_open_real_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ)
    (hlt : (canonicalPeriodicLeft hp hp1 φ heven n).re <
      (canonicalPeriodicRight hp hp1 φ heven n).re) :
    canonicalCriticalOffsetCoefficient hp hp1 φ heven n ≠ 0 := by
  have hgap : canonicalPeriodicGap hp hp1 φ heven n ≠ 0 := by
    intro he
    have heq : canonicalPeriodicRight hp hp1 φ heven n =
        canonicalPeriodicLeft hp hp1 φ heven n := sub_eq_zero.mp he
    have hre := congrArg Complex.re heq
    linarith
  exact canonicalCriticalOffsetCoefficient_ne_zero_of_gap_and_product hp hp1 φ heven n
    hgap (canonicalDeletedPeriodicProduct_ne_zero_at_open_gap_critical
      hp hp1 φ heven hreal n hlt)

/-- The exact squared-gap offset formula holds at every open real gap,
with no restriction to distant indices. -/
theorem canonicalCriticalPoints_midpoint_gap_sq_of_open_real_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ)
    (hlt : (canonicalPeriodicLeft hp hp1 φ heven n).re <
      (canonicalPeriodicRight hp hp1 φ heven n).re) :
    canonicalCriticalPoints hp hp1 φ heven n -
        canonicalPeriodicMidpoint hp hp1 φ heven n =
      (canonicalPeriodicGap hp hp1 φ heven n)^2 *
        canonicalCriticalGapQuotient hp hp1 φ heven n := by
  simpa only [canonicalCriticalMidpointOffset_apply, canonicalCriticalGapQuotient] using
    canonicalCriticalMidpointOffset_eq_gap_sq_mul_quotient hp hp1 φ heven n
      (canonicalCriticalOffsetCoefficient_ne_zero_of_open_real_gap
        hp hp1 φ heven hreal n hlt)

end NLS.ZakharovShabat
