import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.PairNorm

/-! # Exponent inclusions of native weighted pairs

The complex linear inclusion preserves every raw coefficient and composes
exactly, including the Banach endpoints one and infinity.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS
namespace WeightedCoeffPair
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Include native weighted pairs at a larger exponent, retaining both raw sequences. -/
def exponentInclusion (w : Weight) (hpq : p ≤ q) :
    WeightedCoeffPair w p →L[ℂ] WeightedCoeffPair w q :=
  (WithLp.prodContinuousLinearEquiv q ℂ _ _).symm.toContinuousLinearMap.comp
    (((WeightedCoeff.exponentInclusion w hpq).prodMap (WeightedCoeff.exponentInclusion w hpq)).comp
      (WithLp.prodContinuousLinearEquiv p ℂ _ _).toContinuousLinearMap)

@[simp] theorem exponentInclusion_fst (w : Weight) (hpq : p ≤ q)
    (a : WeightedCoeffPair w p) (n : ℤ) :
    (exponentInclusion w hpq a).fst.val n = a.fst.val n :=
  WeightedCoeff.exponentInclusion_apply w hpq a.fst n

@[simp] theorem exponentInclusion_snd (w : Weight) (hpq : p ≤ q)
    (a : WeightedCoeffPair w p) (n : ℤ) :
    (exponentInclusion w hpq a).snd.val n = a.snd.val n :=
  WeightedCoeff.exponentInclusion_apply w hpq a.snd n

theorem exponentInclusion_injective (w : Weight) (hpq : p ≤ q) :
    Function.Injective (exponentInclusion w hpq) := by
  intro a b h
  apply (WithLp.equiv p _).injective
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · change a.fst.val n = b.fst.val n
    simpa only [exponentInclusion_fst] using congrArg (fun c => c.fst.val n) h
  · change a.snd.val n = b.snd.val n
    simpa only [exponentInclusion_snd] using congrArg (fun c => c.snd.val n) h

@[simp] theorem exponentInclusion_refl (w : Weight) (a : WeightedCoeffPair w p) :
    exponentInclusion w le_rfl a = a := by
  apply (WithLp.equiv p _).injective
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · exact exponentInclusion_fst w le_rfl a n
  · exact exponentInclusion_snd w le_rfl a n

@[simp] theorem exponentInclusion_trans {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (w : Weight) (hpq : p ≤ q) (hqr : q ≤ r) (a : WeightedCoeffPair w p) :
    exponentInclusion w hqr (exponentInclusion w hpq a) = exponentInclusion w (hpq.trans hqr) a := by
  apply (WithLp.equiv r _).injective
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · change (exponentInclusion w hqr (exponentInclusion w hpq a)).fst.val n =
      (exponentInclusion w (hpq.trans hqr) a).fst.val n
    simp
  · change (exponentInclusion w hqr (exponentInclusion w hpq a)).snd.val n =
      (exponentInclusion w (hpq.trans hqr) a).snd.val n
    simp
end WeightedCoeffPair

end NLS
