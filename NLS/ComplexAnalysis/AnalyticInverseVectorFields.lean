import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Analytic.Composition

/-! # Analytic vector fields transported by an actual analytic inverse -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def inverseTransportVectorField (f : E → F) (g : F → E) (A : F →L[ℂ] F) (a : E) : E :=
  (fderiv ℂ g (f a)) (A (f a))

theorem analyticOnNhd_inverseTransportVectorField [CompleteSpace E]
    (f : E → F) (g : F → E) (A : F →L[ℂ] F) {V : Set E} {W : Set F}
    (hf : AnalyticOnNhd ℂ f V) (hg : AnalyticOnNhd ℂ g W) (hm : MapsTo f V W) :
    AnalyticOnNhd ℂ (inverseTransportVectorField f g A) V := by
  intro a ha
  have hD := (hg.fderiv (f a) (hm ha)).comp (hf a ha)
  have hA := (A.analyticAt _).comp (hf a ha)
  let B : F →L[ℂ] (F →L[ℂ] E) →L[ℂ] E := ContinuousLinearMap.apply ℂ E
  exact (B.analyticAt_bilinear _).comp₂ hA hD

theorem inverseTransportVectorField_eq_of_pushforward
    (f : E → F) (g : F → E) (A : F →L[ℂ] F) {V : Set E} (hV : IsOpen V)
    (hleft : ∀ a ∈ V, g (f a) = a) (a : E) (ha : a ∈ V)
    (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g (f a))
    (v : E) (hv : (fderiv ℂ f a) v = A (f a)) :
    inverseTransportVectorField f g A a = v := by
  have he : (fun b => g (f b)) =ᶠ[𝓝 a] (fun b : E => b) := by
    filter_upwards [hV.mem_nhds ha] with b hb
    exact hleft b hb
  have hd := (hg.hasFDerivAt.comp a hf.hasFDerivAt).fderiv
  have hid := he.fderiv_eq (𝕜 := ℂ)
  change fderiv ℂ (g ∘ f) a = fderiv ℂ (id : E → E) a at hid
  rw [hd,fderiv_id] at hid
  have hh := congrArg (fun L : E →L[ℂ] E => L v) hid
  change (fderiv ℂ g (f a)) ((fderiv ℂ f a) v) = v at hh
  rwa [hv] at hh

theorem inverseTransportVectorField_pushforward_of_right
    (f : E → F) (g : F → E) (A : F →L[ℂ] F) {W : Set F} (hW : IsOpen W)
    (hright : ∀ b ∈ W, f (g b) = b) (a : E) (ha : f a ∈ W) (hleft : g (f a) = a)
    (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g (f a)) :
    (fderiv ℂ f a) (inverseTransportVectorField f g A a) = A (f a) := by
  have he : (f ∘ g) =ᶠ[𝓝 (f a)] (id : F → F) := by
    filter_upwards [hW.mem_nhds ha] with b hb
    exact hright b hb
  have hfg : DifferentiableAt ℂ f (g (f a)) := by rwa [hleft]
  have hd := (hfg.hasFDerivAt.comp (f a) hg.hasFDerivAt).fderiv
  have hid := he.fderiv_eq (𝕜 := ℂ)
  rw [hd,fderiv_id,hleft] at hid
  exact congrArg (fun L : F →L[ℂ] F => L (A (f a))) hid

end NLS.ComplexAnalysis
