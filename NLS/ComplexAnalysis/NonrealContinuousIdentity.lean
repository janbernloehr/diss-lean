import NLS.ComplexAnalysis.QuadraticEnergySheet

/-! Continuous local functions are determined off the real axis. -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis

theorem ContinuousOn.eqOn_of_nonreal {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f g : ℂ → Y} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (he : ∀ z ∈ U, z.im ≠ 0 → f z=g z) : EqOn f g U := by
  have hfg : EqOn f g (U ∩ {z : ℂ | z.im ≠ 0}) := fun _ hz => he _ hz.1 hz.2
  exact hfg.of_subset_closure hf hg inter_subset_left
    (fun z hz => hU.inter_closure ⟨hz,dense_complex_nonreal z⟩)

end NLS.ComplexAnalysis
