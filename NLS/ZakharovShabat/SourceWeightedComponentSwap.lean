import NLS.ZakharovShabat.SourceComponentSwap
import NLS.ZakharovShabat.SourceWeightedRealSpaces

/-! # Unsigned component exchange in the original weighted source norm -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Bounded component exchange on the original weighted real source.
No spatial or signed-index reflection is applied to its coefficients. -/
def weightedRealSourceComponentSwap (w : SpectralWeight) :
    weightedRealSourceSubmodule (p := p) w →L[ℝ] weightedRealSourceSubmodule (p := p) w := by
  let e := (LinearIsometryEquiv.withLpProdComm p ℂ
    (WeightedCoeff (sourceFrequencyWeight w) p)
    (WeightedCoeff (sourceFrequencyWeight w) p)).toContinuousLinearEquiv.toContinuousLinearMap
  exact ((e.restrictScalars ℝ).comp (weightedRealSourceSubmodule (p := p) w).subtypeL).codRestrict
    (weightedRealSourceSubmodule w) (by
      intro a
      rw [mem_weightedRealSourceSubmodule_iff]
      intro n
      change a.val.fst.val n = conj (a.val.snd.val (-n))
      have hn := (mem_weightedRealSourceSubmodule_iff w a.val).mp a.property (-n)
      rw [hn,neg_neg]
      simp)

@[simp] theorem weightedRealSourceComponentSwap_fst (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    (weightedRealSourceComponentSwap w a).val.fst = a.val.snd := rfl

@[simp] theorem weightedRealSourceComponentSwap_snd (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    (weightedRealSourceComponentSwap w a).val.snd = a.val.fst := rfl

/-- The weighted and unweighted exchanges agree on every original coefficient. -/
theorem originalWeightedRealSource_componentSwap (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    originalWeightedRealSource w (weightedRealSourceComponentSwap w a) =
      realSourceComponentSwap (originalWeightedRealSource w a) := by
  apply Subtype.ext
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · ext n
    change (originalWeightedRealSource w (weightedRealSourceComponentSwap w a)).val.fst n =
      (originalWeightedRealSource w a).val.snd n
    rw [originalWeightedRealSource_fst,originalWeightedRealSource_snd,
      weightedRealSourceComponentSwap_fst]
  · ext n
    change (originalWeightedRealSource w (weightedRealSourceComponentSwap w a)).val.snd n =
      (originalWeightedRealSource w a).val.fst n
    rw [originalWeightedRealSource_snd,originalWeightedRealSource_fst,
      weightedRealSourceComponentSwap_snd]

/-- The bounded weighted map is an involution. -/
@[simp] theorem weightedRealSourceComponentSwap_involutive (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    weightedRealSourceComponentSwap w (weightedRealSourceComponentSwap w a) = a := by
  apply Subtype.ext
  apply (WithLp.equiv p _).injective
  exact Prod.swap_swap (WithLp.ofLp a.val)

/-- Fixed points are exactly equal raw coefficient fields in the native norm. -/
theorem weightedRealSourceComponentSwap_eq_self_iff (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    weightedRealSourceComponentSwap w a = a ↔ a.val.fst = a.val.snd := by
  constructor
  · intro h
    exact (congrArg (fun b : weightedRealSourceSubmodule (p := p) w => b.val.fst) h).symm
  · intro h
    apply Subtype.ext
    apply (WithLp.equiv p _).injective
    exact Prod.ext h.symm h

end NLS.ZakharovShabat
