import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.FourierRealZeroSpatialGenerator

/-! Changing the Banach exponent retains the physical real zero-mode
form and EVERY raw coefficient. In particular this is the literal
Wiener-to-Hilbert inclusion at an unchanged Sobolev order. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

def fourierRealExponentInclusion (w : Weight) (hw : ∀ k, w (-k) = w k) (hpq : p ≤ q) :
    fourierRealZeroSubmodule w p →L[ℝ] fourierRealZeroSubmodule w q :=
  (fourierRealZeroFullProjection w hw).comp
    (((exponentInclusion w hpq).restrictScalars ℝ).comp
      (((zeroModeSubmodule w p).subtypeL.restrictScalars ℝ).comp
        (fourierRealZeroSubmodule w p).subtypeL))

theorem fourierRealExponentInclusion_apply (w : Weight) (hw : ∀ k, w (-k) = w k) (hpq : p ≤ q)
    (a : fourierRealZeroSubmodule w p) (k : ℤ) :
    (fourierRealExponentInclusion w hw hpq a).val.val.val k = a.val.val.val k := by
  let b := exponentInclusion w hpq a.val.val
  have hb (j : ℤ) : b.val j = a.val.val.val j := exponentInclusion_apply w hpq a.val.val j
  have h0 : b.val 0 = 0 := (hb 0).trans a.val.property
  have hr (j : ℤ) : b.val (-j) = (starRingEnd ℂ) (b.val j) := by
    rw [hb, hb]
    exact a.property j
  have he := fourierRealZeroFullProjection_inclusion w hw (⟨⟨b,h0⟩,hr⟩ : fourierRealZeroSubmodule w q)
  change (fourierRealZeroFullProjection w hw b).val.val.val k = _
  rw [he]
  exact hb k

theorem fourierRealExponentInclusion_injective (w : Weight) (hw : ∀ k, w (-k) = w k) (hpq : p ≤ q) :
    Function.Injective (fourierRealExponentInclusion w hw hpq) := by
  intro a b he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  have h := congrArg (fun z => z.val.val.val k) he
  simpa only [fourierRealExponentInclusion_apply] using h

end NLS.WeightedCoeff
