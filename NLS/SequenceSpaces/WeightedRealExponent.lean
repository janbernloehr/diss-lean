import NLS.SequenceSpaces.WeightedRealCoeff
import NLS.SequenceSpaces.ExponentEmbedding
import Mathlib.Analysis.Normed.Lp.ProdLp

/-! # Exponent inclusion for original weighted real sequences

The maps preserve raw coefficients, including negative and zero frequencies.
They use the inherited weighted norms and the actual lp pair topologies.
The coefficient inclusion is contractive at every Banach exponent.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedRealCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Increase the exponent without changing any original real weighted coefficient. -/
def exponentInclusion (w : Weight) (hpq : p ≤ q) :
    WeightedRealCoeff w p →L[ℝ] WeightedRealCoeff w q :=
  (((WeightedCoeff.exponentInclusion w hpq).restrictScalars ℝ).comp
    (complexCLM w p)).codRestrict (WeightedCoeff.realSubmodule w q) (by
      intro a
      rw [WeightedCoeff.mem_realSubmodule_iff]
      intro n
      simpa using im_eq_zero w p a n)

@[simp] theorem exponentInclusion_apply (w : Weight) (hpq : p ≤ q)
    (a : WeightedRealCoeff w p) (n : ℤ) :
    (exponentInclusion w hpq a).val.val n = a.val.val n :=
  WeightedCoeff.exponentInclusion_apply w hpq a.val n

theorem exponentInclusion_injective (w : Weight) (hpq : p ≤ q) :
    Function.Injective (exponentInclusion w hpq) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  funext n
  simpa only [exponentInclusion_apply] using congrArg (fun c => c.val.val n) h

/-- The weighted real coefficient inclusion is contractive. -/
theorem norm_exponentInclusion_le (w : Weight) (hpq : p ≤ q)
    (a : WeightedRealCoeff w p) : ‖exponentInclusion w hpq a‖ ≤ ‖a‖ :=
  WeightedCoeff.norm_exponentInclusion_le w hpq a.val

@[simp] theorem exponentInclusion_refl (w : Weight) (a : WeightedRealCoeff w p) :
    exponentInclusion w le_rfl a = a := by
  apply Subtype.ext
  apply Subtype.ext
  funext n
  exact exponentInclusion_apply w le_rfl a n

@[simp] theorem exponentInclusion_trans {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (w : Weight) (hpq : p ≤ q) (hqr : q ≤ r) (a : WeightedRealCoeff w p) :
    exponentInclusion w hqr (exponentInclusion w hpq a) =
      exponentInclusion w (hpq.trans hqr) a := by
  apply Subtype.ext
  apply Subtype.ext
  funext n
  simp only [exponentInclusion_apply]

/-- The original target pair inclusion uses the source and target exponents' own lp norms. -/
def pairExponentInclusion (w : Weight) (hpq : p ≤ q) :
    WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p) →L[ℝ]
      WithLp q (WeightedRealCoeff w q × WeightedRealCoeff w q) :=
  (WithLp.prodContinuousLinearEquiv q ℝ _ _).symm.toContinuousLinearMap.comp
    (((exponentInclusion w hpq).prodMap (exponentInclusion w hpq)).comp
      (WithLp.prodContinuousLinearEquiv p ℝ _ _).toContinuousLinearMap)

@[simp] theorem pairExponentInclusion_fst (w : Weight) (hpq : p ≤ q)
    (a : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    (pairExponentInclusion w hpq a).fst = exponentInclusion w hpq a.fst := rfl

@[simp] theorem pairExponentInclusion_snd (w : Weight) (hpq : p ≤ q)
    (a : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    (pairExponentInclusion w hpq a).snd = exponentInclusion w hpq a.snd := rfl

theorem pairExponentInclusion_injective (w : Weight) (hpq : p ≤ q) :
    Function.Injective (pairExponentInclusion w hpq) := by
  intro a b h
  apply (WithLp.equiv p _).injective
  exact Prod.ext
    (exponentInclusion_injective w hpq (congrArg WithLp.fst h))
    (exponentInclusion_injective w hpq (congrArg WithLp.snd h))

@[simp] theorem pairExponentInclusion_refl (w : Weight)
    (a : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    pairExponentInclusion w le_rfl a = a := by
  apply (WithLp.equiv p _).injective
  exact Prod.ext (exponentInclusion_refl w a.fst) (exponentInclusion_refl w a.snd)

@[simp] theorem pairExponentInclusion_trans {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (w : Weight) (hpq : p ≤ q) (hqr : q ≤ r)
    (a : WithLp p (WeightedRealCoeff w p × WeightedRealCoeff w p)) :
    pairExponentInclusion w hqr (pairExponentInclusion w hpq a) =
      pairExponentInclusion w (hpq.trans hqr) a := by
  apply (WithLp.equiv r _).injective
  exact Prod.ext (exponentInclusion_trans w hpq hqr a.fst)
    (exponentInclusion_trans w hpq hqr a.snd)
end NLS.WeightedRealCoeff
