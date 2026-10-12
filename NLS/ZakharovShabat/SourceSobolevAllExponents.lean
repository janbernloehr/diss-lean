import NLS.ZakharovShabat.SourceSobolevEmbedding
import NLS.SequenceSpaces.SobolevEmbedding
import NLS.SequenceSpaces.PairExponentEmbedding

/-! # The original H1 source in every coefficient exponent

Sobolev summability gives l1 coefficients, which include continuously into
every source exponent at least one. All maps preserve both raw sequences.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual period-one H1 coefficients in any source exponent at least one. -/
def sobolevSourceExponentInclusion (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] CoeffPair p :=
  let S := (Coeff.exponentInclusion (show (1 : ℝ≥0∞) ≤ p from Fact.out)).comp
    (WeightedCoeff.sobolevToL1CLM 2 (by simp))
  (CoeffPair.toMax p).symm.toContinuousLinearMap.comp (S.prodMap S)

@[simp] theorem sobolevSourceExponentInclusion_fst (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    (sobolevSourceExponentInclusion p a).fst n = a.1.val n := by
  change Coeff.exponentInclusion (show (1 : ℝ≥0∞) ≤ p from Fact.out)
    (WeightedCoeff.sobolevToL1CLM 2 (by simp) a.1) n = _
  simp

@[simp] theorem sobolevSourceExponentInclusion_snd (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : ScalarDomain 2 × ScalarDomain 2) (n : ℤ) :
    (sobolevSourceExponentInclusion p a).snd n = a.2.val n := by
  change Coeff.exponentInclusion (show (1 : ℝ≥0∞) ≤ p from Fact.out)
    (WeightedCoeff.sobolevToL1CLM 2 (by simp) a.2) n = _
  simp

/-- The new map agrees with the established Hilbert source inclusion. -/
@[simp] theorem sobolevSourceExponentInclusion_two (a : ScalarDomain 2 × ScalarDomain 2) :
    sobolevSourceExponentInclusion 2 a = sobolevSourceInclusion a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n <;> simp

/-- Source exponent inclusion preserves the original H1 input exactly. -/
@[simp] theorem exponentInclusion_sobolevSourceExponentInclusion
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hpq : p ≤ q)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    CoeffPair.exponentInclusion hpq (sobolevSourceExponentInclusion p a) =
      sobolevSourceExponentInclusion q a := by
  apply (CoeffPair.toMax q).injective
  apply Prod.ext <;> ext n <;> simp

end NLS.ZakharovShabat
