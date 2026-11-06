import NLS.ComplexAnalysis.ParametricConvexPrimitive
import NLS.ComplexAnalysis.MovingSpectralParameter
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- A normalized analytic primitive is stationary when its density is
stationary. The anchor removes the otherwise undetermined constant. -/
theorem normalizedPrimitive_source_fderiv_eq_zero
    (P F : ℂ × A → ℂ) (Ω : Set ℂ) (V : Set A) (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hconn : IsPreconnected Ω) (c : ℂ) (hc : c∈Ω) (p h : A) (hp : p∈V)
    (hP : AnalyticOnNhd ℂ P (Ω ×ˢ V))
    (hderiv : ∀ b∈V, ∀ z∈Ω, HasDerivAt (fun w => P (w,b)) (F (z,b)) z)
    (hanchor : ∀ b∈V, P (c,b)=0)
    (hzero : ∀ z∈Ω, (fderiv ℂ (fun b : A => F (z,b)) p) h=0)
    (z : ℂ) (hz : z∈Ω) :
    (fderiv ℂ (fun b : A => P (z,b)) p) h=0 := by
  let J : ℂ → ℂ := fun w => (fderiv ℂ (fun b : A => P (w,b)) p) h
  let ev : ((ℂ × A) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,h)
  have hJjoint : AnalyticOnNhd ℂ (fun t => (fderiv ℂ P t) (0,h)) (Ω ×ˢ V) :=
    ev.comp_analyticOnNhd hP.fderiv
  have hJ : AnalyticOnNhd ℂ J Ω := by
    intro w hw
    have ha := (hJjoint (w,p) ⟨hw,hp⟩).comp
      (f := fun w : ℂ => (w,p)) (analyticAt_id.prod analyticAt_const)
    have he : J=ᶠ[𝓝 w] (fun t => (fderiv ℂ P (t,p)) (0,h)) := by
      filter_upwards [hΩ.mem_nhds hw] with t ht
      dsimp only [J]
      rw [fderiv_source_section_eq_joint P t p (hP (t,p) ⟨ht,hp⟩).differentiableAt]
      rfl
    exact ha.congr he.symm
  have hdz (w : ℂ) (hw : w∈Ω) : deriv J w=0 := by
    rw [← fderiv_source_deriv_spectral_eq_deriv_spectral_fderiv_source P (Ω ×ˢ V)
      (hΩ.prod hV) hP w p ⟨hw,hp⟩ h]
    have he : (fun b : A => deriv (fun t => P (t,b)) w)=ᶠ[𝓝 p] (fun b => F (w,b)) := by
      filter_upwards [hV.mem_nhds hp] with b hb
      exact (hderiv b hb w hw).deriv
    rw [he.fderiv_eq,hzero w hw]
  have hJc : J c=0 := by
    have he : (fun b : A => P (c,b))=ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := by
      filter_upwards [hV.mem_nhds hp] with b hb
      exact hanchor b hb
    dsimp only [J]
    rw [he.fderiv_eq,fderiv_const_apply,zero_apply]
  have he := hΩ.is_const_of_deriv_eq_zero hconn hJ.differentiableOn (fun w hw => hdz w hw) hz hc
  exact he.trans hJc

theorem parametricConvexPrimitive_source_fderiv_eq_zero
    (F : ℂ × A → ℂ) (Ω : Set ℂ) (V : Set A) (c : ℂ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hV : IsOpen V) (hc : c∈Ω)
    (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V)) (p h : A) (hp : p∈V)
    (hzero : ∀ z∈Ω, (fderiv ℂ (fun b : A => F (z,b)) p) h=0)
    (z : ℂ) (hz : z∈Ω) :
    (fderiv ℂ (fun b : A => parametricConvexPrimitive F c (z,b)) p) h=0 := by
  apply normalizedPrimitive_source_fderiv_eq_zero (parametricConvexPrimitive F c) F Ω V hΩ hV
    hconv.isPreconnected c hc p h hp (analyticOnNhd_parametricConvexPrimitive F Ω V c hΩ hconv hV hc hF)
    (fun b hb w hw => hasDerivAt_parametricConvexPrimitive F Ω V c hΩ hconv hc hF b hb w hw)
    (fun b _ => parametricConvexPrimitive_anchor F c b) hzero z hz

/-- With a stationary density, the derivative of the actual moving
terminal primitive is precisely its finite terminal differential. -/
theorem parametricConvexPrimitive_moving_terminal_fderiv_of_source_kernel
    (F : ℂ × A → ℂ) (Ω : Set ℂ) (V : Set A) (c : ℂ)
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) (hV : IsOpen V) (hc : c∈Ω)
    (hF : AnalyticOnNhd ℂ F (Ω ×ˢ V)) (μ : A → ℂ) (p h : A) (hp : p∈V)
    (hμ : AnalyticAt ℂ μ p) (hμΩ : μ p∈Ω)
    (hzero : ∀ z∈Ω, (fderiv ℂ (fun b : A => F (z,b)) p) h=0) :
    (fderiv ℂ (fun b : A => parametricConvexPrimitive F c (μ b,b)) p) h=
      F (μ p,p)*((fderiv ℂ μ p) h) := by
  have hP := analyticOnNhd_parametricConvexPrimitive F Ω V c hΩ hconv hV hc hF
  rw [fderiv_moving_spectral_parameter (parametricConvexPrimitive F c) μ p
    (hP (μ p,p) ⟨hμΩ,hp⟩).differentiableAt hμ.differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [parametricConvexPrimitive_source_fderiv_eq_zero F Ω V c hΩ hconv hV hc hF p h hp hzero (μ p) hμΩ,
    (hasDerivAt_parametricConvexPrimitive F Ω V c hΩ hconv hc hF p hp (μ p) hμΩ).deriv,zero_add]

end NLS.ComplexAnalysis
