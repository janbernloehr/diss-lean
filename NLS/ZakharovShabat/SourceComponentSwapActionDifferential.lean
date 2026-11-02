import NLS.ZakharovShabat.SourceComponentSwapActions
import NLS.ZakharovShabat.SourceComplexActionAnalytic
import NLS.ZakharovShabat.SourceHolomorphicRealGerm

/-! # The full complex action differential under component exchange

The actual real-source action identity determines the holomorphic germ.
Its derivative therefore transports every complex source direction, including
at closed gaps; the conclusion is not limited to real tangent directions.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Component exchange intertwines the original complex action germs at
every real source, including all collapsed gaps. -/
theorem eventually_sourceComplexAction_componentSwap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (sourceComplexAction hp hp1 n ∘ sourceComponentSwap) =ᶠ[𝓝 φ.val]
      sourceComplexAction hp hp1 (-n) := by
  apply eventuallyEq_source_of_analyticAt_of_real_agreement hp φ _ _
  · exact (analyticAt_sourceComplexAction_of_realType hp hp1 n
      (sourceComponentSwap φ.val) (sourceComponentSwap_realType φ.val φ.property)).comp
      (f := sourceComponentSwap) (x := φ.val)
      ((sourceComponentSwap (p := p)).toContinuousLinearEquiv.analyticAt _)
  · exact analyticAt_sourceComplexAction_of_realType hp hp1 (-n) φ.val φ.property
  · intro χ
    exact sourceComplexAction_componentSwap hp hp1 χ n

/-- The entire original complex action cotangent has the reflected index,
with the actual bounded source swap applied to its argument. -/
theorem fderiv_sourceComplexAction_componentSwap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    (fderiv ℂ (sourceComplexAction hp hp1 n) (sourceComponentSwap φ.val)).comp
      sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap =
        fderiv ℂ (sourceComplexAction hp hp1 (-n)) φ.val := by
  have he := (eventually_sourceComplexAction_componentSwap hp hp1 φ n).fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp φ.val
    (analyticAt_sourceComplexAction_of_realType hp hp1 n (sourceComponentSwap φ.val)
      (sourceComponentSwap_realType φ.val φ.property)).differentiableAt
    (sourceComponentSwap (p := p)).toContinuousLinearEquiv.differentiableAt] at he
  have hs : fderiv ℂ (sourceComponentSwap (p := p)) φ.val =
      sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap :=
    (sourceComponentSwap (p := p)).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.fderiv
  rw [hs] at he
  exact he

end NLS.ZakharovShabat
