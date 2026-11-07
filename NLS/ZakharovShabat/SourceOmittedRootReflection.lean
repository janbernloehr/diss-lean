import NLS.ZakharovShabat.SourceCanonicalRootReflection
import NLS.ZakharovShabat.SourceStandardRootOmittedProduct

/-! Reflection of the actual omitted root product on the full cut
complement. Both the full root and selected root change sign. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourcePeriodicReflection.omittedProduct_neg
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p}
    (h : SourcePeriodicReflection hp hp1 ψ) (m : ℤ) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceStandardRootOmittedProduct hp hp1 (-m) ψ (-z) =
      sourceStandardRootOmittedProduct hp hp1 m ψ z := by
  have he := h.canonicalRoot_neg z
  rw [sourceCanonicalRoot_eq_omitted hp hp1 (-m),sourceCanonicalRoot_eq_omitted hp hp1 m,
    h.standardRoot_neg m z] at he
  have hQ := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z (hz m)
  apply mul_left_cancel₀ (mul_ne_zero (by simp : (2*I:ℂ) ≠ 0) hQ)
  linear_combination -he

end NLS.ZakharovShabat
