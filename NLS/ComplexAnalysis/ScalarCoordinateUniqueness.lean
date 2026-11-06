import NLS.ComplexAnalysis.BoundaryAnalyticCoordinate

/-! # Local uniqueness of continuous lifts through a regular scalar coordinate -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis

/-- A regular scalar coordinate determines the germ of any continuous lift. -/
theorem eventuallyEq_of_regular_scalar_coordinate
    {X : Type*} [TopologicalSpace X] (φ : ℂ → ℂ) (f g : X → ℂ) (x : X)
    (hφ : AnalyticAt ℂ φ (g x)) (hne : deriv φ (g x) ≠ 0)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hbase : f x = g x)
    (heq : ∀ᶠ y in 𝓝 x, φ (f y) = φ (g y)) : f =ᶠ[𝓝 x] g := by
  let r := hφ.hasStrictDerivAt.localInverse _ _ _ hne
  have hleft : ∀ᶠ w in 𝓝 (g x), r (φ w) = w :=
    hφ.hasStrictDerivAt.eventually_left_inverse hne
  have hfl : ∀ᶠ y in 𝓝 x, r (φ (f y)) = f y := by
    have ht := hf.tendsto
    rw [hbase] at ht
    exact ht.eventually hleft
  have hgl : ∀ᶠ y in 𝓝 x, r (φ (g y)) = g y := hg.tendsto.eventually hleft
  filter_upwards [hfl,hgl,heq] with y hyf hyg hy
  exact hyf.symm.trans ((congrArg r hy).trans hyg)

end NLS.ComplexAnalysis
