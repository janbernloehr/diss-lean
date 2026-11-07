import Mathlib.Topology.Algebra.Group.Basic

/-! A local inverse of an equivariant map preserves the fixed points of
continuous symmetries near a fixed base point. Only the genuine two-sided
local inverse identities and continuity are used. -/
open Filter Topology
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

theorem eventually_localInverse_fixedPoints (f : E → F) (g : F → E)
    (e : E → E) (s : F → F) (x : E)
    (he : ContinuousAt e x) (hex : e x=x)
    (heq : ∀ y, f (e y)=s (f y))
    (hg : Tendsto g (𝓝 (f x)) (𝓝 x))
    (hleft : ∀ᶠ y in 𝓝 x, g (f y)=y)
    (hright : ∀ᶠ z in 𝓝 (f x), f (g z)=z) :
    ∀ᶠ z in 𝓝 (f x), s z=z → e (g z)=g z := by
  have ht : Tendsto (fun z => e (g z)) (𝓝 (f x)) (𝓝 x) := by
    simpa only [hex,Function.comp_def] using he.tendsto.comp hg
  filter_upwards [ht.eventually hleft,hright] with z hz hr hs
  rw [heq,hr,hs] at hz
  exact hz.symm

end NLS.FunctionalAnalysis
