import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Analytic.Linear

/-! # Stationarity in actual inverse coordinates from conserved complete orbits -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E F H : Type*}
  [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem fderiv_inverse_coordinates_eq_zero_of_orbit
    (f : E → F) (g : F → E) (h : E → H) {U : Set E} (hU : IsOpen U)
    (hl : ∀ a ∈ U, g (f a) = a) (z : F) (hz : g z ∈ U)
    (C : ℝ → E) (hC : ContinuousAt C 0) (hC0 : C 0 = g z)
    (T : ℝ → F) (hT0 : T 0 = z) (v : F) (hT : HasDerivAt T v 0)
    (hcov : ∀ t, f (C t) = T t) (hinv : ∀ t, h (C t) = h (g z))
    (hHg : DifferentiableAt ℂ (fun y => h (g y)) z) :
    fderiv ℂ (fun y => h (g y)) z v = 0 := by
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), C t ∈ U := by
    have h := hC.tendsto.eventually (hU.mem_nhds (hC0.symm ▸ hz))
    exact h
  have he : (fun t => h (g (T t))) =ᶠ[𝓝 (0 : ℝ)] fun _ => h (g z) := by
    filter_upwards [hnear] with t ht
    rw [← hcov t,hl (C t) ht,hinv t]
  have hd : HasFDerivAt (fun y => h (g y))
      ((fderiv ℂ (fun y => h (g y)) z).restrictScalars ℝ) (T 0) := by
    rw [hT0]
    exact hHg.hasFDerivAt.restrictScalars ℝ
  have hh := hd.comp_hasDerivAt 0 hT
  have hc : HasDerivAt (fun t => h (g (T t))) 0 0 :=
    (hasDerivAt_const 0 (h (g z))).congr_of_eventuallyEq he
  exact hh.unique hc

theorem analyticAt_fderiv_apply_clm
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    {f : A → B} {a : A} (hf : AnalyticAt ℂ f a) (K : A →L[ℂ] A) :
    AnalyticAt ℂ (fun z => fderiv ℂ f z (K z)) a :=
  ((ContinuousLinearMap.apply (E := A) ℂ B).analyticAt_bilinear _).comp₂ (K.analyticAt a) hf.fderiv

end NLS.ComplexAnalysis
