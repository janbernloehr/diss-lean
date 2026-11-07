import NLS.ZakharovShabat.Domain

/-! Continuous equality on an open finite-p source domain can be checked
on the dense one-derivative scalar domain. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem eqOn_of_eqOn_scalarInclusion {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] {U : Set (Coeff p)} (hU : IsOpen U)
    {f g : Coeff p → Y} (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : ∀ a : ScalarDomain p, scalarInclusion a ∈ U → f (scalarInclusion a) = g (scalarInclusion a)) :
    EqOn f g U := by
  have hfg : EqOn f g (U ∩ range (scalarInclusion (p := p))) := by
    rintro _ ⟨ha,a,rfl⟩
    exact he a ha
  exact hfg.of_subset_closure hf hg inter_subset_left
    (fun a ha => hU.inter_closure ⟨ha,scalarInclusion_denseRange hp a⟩)

end NLS.ZakharovShabat
