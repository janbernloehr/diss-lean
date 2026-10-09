import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Transport of local analytic extensions along parameter maps -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E E' F S S' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace S] [TopologicalSpace S']

/-- A continuous parameter change compatible with an ambient complex linear
coordinate change transports local extension germs. -/
theorem localAnalyticExtensions_transport
    (e : E' ≃L[ℂ] E) (h : S' → S) (hh : Continuous h)
    (i : S → E) (i' : S' → E') (hi : ∀ x, i (h x) = e (i' x))
    {f : S → F} {U : Set S}
    (hf : ∀ x ∈ U, ∃ g : E → F, AnalyticAt ℂ g (i x) ∧ f =ᶠ[𝓝 x] (g ∘ i)) :
    ∀ x ∈ h ⁻¹' U, ∃ g : E' → F,
      AnalyticAt ℂ g (i' x) ∧ (f ∘ h) =ᶠ[𝓝 x] (g ∘ i') := by
  intro x hx
  obtain ⟨g,hg,he⟩ := hf (h x) hx
  refine ⟨g ∘ e, hg.comp_of_eq (e.analyticAt (i' x)) (hi x).symm,?_⟩
  filter_upwards [he.comp_tendsto hh.continuousAt] with y hy
  change f (h y) = g (e (i' y))
  change f (h y) = g (i (h y)) at hy
  rwa [hi y] at hy

/-- Relative openness and density are unchanged by a homeomorphism. -/
theorem open_dense_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {U S : Set X}
    (h : IsOpen (e.symm ⁻¹' S) ∧ e.symm ⁻¹' U ⊆ closure (e.symm ⁻¹' S)) :
    IsOpen S ∧ U ⊆ closure S := by
  refine ⟨?_,?_⟩
  · have ho := h.1.preimage e.continuous
    have heq : e ⁻¹' (e.symm ⁻¹' S) = S := by
      ext x
      change (e.symm (e x) ∈ S) ↔ x ∈ S
      rw [e.symm_apply_apply]
    rwa [heq] at ho
  · intro x hx
    have he : e x ∈ closure (e.symm ⁻¹' S) := h.2 (by simpa using hx)
    rw [← e.symm.preimage_closure] at he
    simpa only [mem_preimage,e.symm_apply_apply] using he

end NLS.ComplexAnalysis
