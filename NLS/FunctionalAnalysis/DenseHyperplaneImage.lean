import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Dense images after removing a scalar trace

A dense continuous linear image stays dense after restriction to a trace
kernel if trace-one corrections have images tending to zero. No reflexivity
or implicit Hilbert-space identification is needed.
-/
noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis
variable {𝕜 V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Correcting the trace in an asymptotically invisible direction preserves a dense image. -/
theorem denseRange_restrict_ker_of_vanishing_trace
    (A : V →L[𝕜] W) (tau : V →L[𝕜] 𝕜) (hA : DenseRange A)
    (e : ℕ → V) (he : ∀ n, tau (e n) = 1)
    (hAe : Tendsto (A ∘ e) atTop (𝓝 0)) :
    DenseRange (A.comp tau.ker.subtypeL) := by
  have hs : range A ⊆ closure (range (A.comp tau.ker.subtypeL)) := by
    rintro _ ⟨f, rfl⟩
    let g : ℕ → tau.ker := fun n => ⟨f-tau f • e n, by
      change tau (f-tau f • e n) = 0
      rw [map_sub, map_smul, he n, smul_eq_mul, mul_one, sub_self]⟩
    have ht : Tendsto (fun n => A (g n).val) atTop (𝓝 (A f)) := by
      have h := (tendsto_const_nhds (x := A f)).sub (hAe.const_smul (tau f))
      simpa only [Function.comp_def, g, map_sub, map_smul, smul_zero, sub_zero] using h
    exact mem_closure_of_tendsto ht (Eventually.of_forall fun n => ⟨g n, rfl⟩)
  intro w
  exact closure_minimal hs isClosed_closure (hA w)

end NLS.FunctionalAnalysis
