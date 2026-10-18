import NLS.ComplexAnalysis.OrderedGapSeparation
import NLS.ZakharovShabat.CanonicalPeriodicGapOrder
import NLS.ZakharovShabat.SourcePrimitivePowerPositive

/-! # Uniform separation of actual real spectral gaps

Strict ordering of the original periodic endpoints separates each fixed
gap from every other gap, including collapsed exterior gaps.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every actual real gap has a uniformly separated exterior containing all other closed gaps. -/
theorem sourceRealGaps_uniform_exterior_separation (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    let L : ℤ → ℝ := fun k => (canonicalPeriodicLeft hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k).re
    let R : ℤ → ℝ := fun k => (canonicalPeriodicRight hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k).re
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, m ≠ n → ∀ x ∈ Icc (L m) (R m),
      δ ≤ |x-L n| ∧ δ ≤ |x-R n| ∧ (R n-L n)/2+δ ≤ |x-(L n+R n)/2| := by
  apply NLS.ComplexAnalysis.ordered_gaps_uniform_exterior_separation
  · intro k
    exact NLS.ComplexAnalysis.re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val)).2.1 k)
  · intro i j hij
    exact canonicalPeriodicRight_re_lt_left_of_lt hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) hij

end NLS.ZakharovShabat
