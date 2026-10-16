import NLS.ZakharovShabat.SourceWeightedRealSpaces
import NLS.ZakharovShabat.SourceBoundaryExponentDifferential

/-! # Exponent inclusion for original weighted real sources

The continuous real linear inclusion preserves both raw Fourier sequences
and the conjugate-reflection relation. It is injective, composes exactly,
and agrees with the unweighted source inclusion after forgetting weights.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Include the original weighted real source at a larger exponent, preserving its reality relation. -/
def weightedRealSourceExponentInclusion (w : SpectralWeight) (hpq : p ≤ q) :
    weightedRealSourceSubmodule (p := p) w →L[ℝ] weightedRealSourceSubmodule (p := q) w := by
  let e : WeightedCoeffPair (sourceFrequencyWeight w) p →L[ℂ]
      WeightedCoeffPair (sourceFrequencyWeight w) q :=
    (WithLp.prodContinuousLinearEquiv q ℂ _ _).symm.toContinuousLinearMap.comp
      (((WeightedCoeff.exponentInclusion (sourceFrequencyWeight w) hpq).prodMap
        (WeightedCoeff.exponentInclusion (sourceFrequencyWeight w) hpq)).comp
        (WithLp.prodContinuousLinearEquiv p ℂ _ _).toContinuousLinearMap)
  exact ((e.restrictScalars ℝ).comp (weightedRealSourceSubmodule (p := p) w).subtypeL).codRestrict
    (weightedRealSourceSubmodule (p := q) w) (by
      intro a
      rw [mem_weightedRealSourceSubmodule_iff]
      intro n
      change (WeightedCoeff.exponentInclusion (sourceFrequencyWeight w) hpq a.val.snd).val n =
        starRingEnd ℂ ((WeightedCoeff.exponentInclusion (sourceFrequencyWeight w) hpq a.val.fst).val (-n))
      simpa using (mem_weightedRealSourceSubmodule_iff w a.val).mp a.property n)

@[simp] theorem weightedRealSourceExponentInclusion_fst (w : SpectralWeight) (hpq : p ≤ q)
    (a : weightedRealSourceSubmodule (p := p) w) (n : ℤ) :
    (weightedRealSourceExponentInclusion w hpq a).val.fst.val n = a.val.fst.val n :=
  WeightedCoeff.exponentInclusion_apply (sourceFrequencyWeight w) hpq a.val.fst n

@[simp] theorem weightedRealSourceExponentInclusion_snd (w : SpectralWeight) (hpq : p ≤ q)
    (a : weightedRealSourceSubmodule (p := p) w) (n : ℤ) :
    (weightedRealSourceExponentInclusion w hpq a).val.snd.val n = a.val.snd.val n :=
  WeightedCoeff.exponentInclusion_apply (sourceFrequencyWeight w) hpq a.val.snd n

theorem weightedRealSourceExponentInclusion_injective (w : SpectralWeight) (hpq : p ≤ q) :
    Function.Injective (weightedRealSourceExponentInclusion w hpq) := by
  intro a b h
  apply Subtype.ext
  apply (WithLp.equiv p _).injective
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · change a.val.fst.val n = b.val.fst.val n
    simpa only [weightedRealSourceExponentInclusion_fst] using congrArg (fun c => c.val.fst.val n) h
  · change a.val.snd.val n = b.val.snd.val n
    simpa only [weightedRealSourceExponentInclusion_snd] using congrArg (fun c => c.val.snd.val n) h

@[simp] theorem weightedRealSourceExponentInclusion_refl (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    weightedRealSourceExponentInclusion w le_rfl a = a := by
  apply Subtype.ext
  apply (WithLp.equiv p _).injective
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · exact weightedRealSourceExponentInclusion_fst w le_rfl a n
  · exact weightedRealSourceExponentInclusion_snd w le_rfl a n

@[simp] theorem weightedRealSourceExponentInclusion_trans {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (w : SpectralWeight) (hpq : p ≤ q) (hqr : q ≤ r)
    (a : weightedRealSourceSubmodule (p := p) w) :
    weightedRealSourceExponentInclusion w hqr (weightedRealSourceExponentInclusion w hpq a) =
      weightedRealSourceExponentInclusion w (hpq.trans hqr) a := by
  apply Subtype.ext
  apply (WithLp.equiv r _).injective
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · exact (weightedRealSourceExponentInclusion_fst w hqr _ n).trans
      ((weightedRealSourceExponentInclusion_fst w hpq a n).trans
        (weightedRealSourceExponentInclusion_fst w (hpq.trans hqr) a n).symm)
  · exact (weightedRealSourceExponentInclusion_snd w hqr _ n).trans
      ((weightedRealSourceExponentInclusion_snd w hpq a n).trans
        (weightedRealSourceExponentInclusion_snd w (hpq.trans hqr) a n).symm)

/-- Weighted and unweighted exponent inclusions have exactly the same original source coefficients. -/
@[simp] theorem originalWeightedRealSource_exponent (w : SpectralWeight) (hpq : p ≤ q)
    (a : weightedRealSourceSubmodule (p := p) w) :
    originalWeightedRealSource w (weightedRealSourceExponentInclusion w hpq a) =
      realTypeSourceExponentInclusion hpq (originalWeightedRealSource w a) := by
  apply Subtype.ext
  apply (WithLp.equiv q _).injective
  apply Prod.ext <;> apply lp.ext <;> funext n
  · change (originalWeightedRealSource w (weightedRealSourceExponentInclusion w hpq a)).val.fst n =
      (Coeff.exponentInclusion hpq (originalWeightedRealSource w a).val.fst) n
    simp
  · change (originalWeightedRealSource w (weightedRealSourceExponentInclusion w hpq a)).val.snd n =
      (Coeff.exponentInclusion hpq (originalWeightedRealSource w a).val.snd) n
    simp

end NLS.ZakharovShabat
