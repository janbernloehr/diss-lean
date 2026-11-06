import NLS.ComplexAnalysis.AnalyticOpenInverse

/-! # Invertible analytic jets give injective derivatives on a common open domain -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.ComplexAnalysis

/-- The actual analytic map has injective derivatives throughout ONE
open neighborhood of an invertible jet, using its actual analytic inverse. -/
theorem exists_open_injective_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : E → E) (U : Set E) (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (q : E) (hq : q∈U) (hu : IsUnit (fderiv ℂ f q)) :
    ∃ V : Set E, IsOpen V ∧ q∈V ∧ V⊆U ∧ ∀ p∈V, Function.Injective (fderiv ℂ f p) := by
  obtain ⟨V,W,hV,_hW,hqV,_hfqW,hVU,_himage,hbij,g,hfa,hga,hleft,_hright⟩ :=
    exists_analytic_inverse_open_sets hU hf hq hu
  refine ⟨V,hV,hqV,hVU,?_⟩
  intro p hp
  have he : (fun x => g (f x)) =ᶠ[𝓝 p] (fun x => x) :=
    Filter.eventuallyEq_of_mem (hV.mem_nhds hp) hleft
  have hd : fderiv ℂ (fun x => g (f x)) p=(fderiv ℂ g (f p)).comp (fderiv ℂ f p) :=
    ((hga (f p) (hbij.mapsTo hp)).differentiableAt.hasFDerivAt.comp p
      (hfa p hp).differentiableAt.hasFDerivAt).fderiv
  have hcomp : (fderiv ℂ g (f p)).comp (fderiv ℂ f p)=ContinuousLinearMap.id ℂ E := by
    have h : fderiv ℂ (fun x => g (f x)) p=fderiv ℂ (fun x : E => x) p := he.fderiv_eq
    have hid : fderiv ℂ (fun x : E => x) p=ContinuousLinearMap.id ℂ E := fderiv_id
    rw [hd,hid] at h
    exact h
  have hl : Function.LeftInverse (fderiv ℂ g (f p)) (fderiv ℂ f p) := by
    intro x
    exact congrArg (fun A : E →L[ℂ] E => A x) hcomp
  exact hl.injective

end NLS.ComplexAnalysis
