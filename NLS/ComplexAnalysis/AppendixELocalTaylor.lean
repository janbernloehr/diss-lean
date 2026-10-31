import NLS.ComplexAnalysis.RealComplexification
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Local derivative and series assertions in the proof of E.2

The existing complex-line identity argument supplies the zero germ.
Every iterated derivative and every power-series diagonal then vanishes.
No connectedness is needed for these local assertions.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {R E F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- At every real point, vanishing on the real slice gives a zero analytic germ. -/
theorem sourceLemmaE2_zero_germ (c : RealComplexification R E) (U : Set E)
    (hU : IsOpen U) {u : E} (hu : u ∈ U ∩ c.realLocus)
    (f : E → F) (hf : AnalyticOnNhd ℂ f U) (hzero : EqOn f 0 (U ∩ c.realLocus)) :
    f =ᶠ[𝓝 u] 0 :=
  DifferentiableOn.eventually_eq_zero_of_continuous_real_form c.realLocus u hu.2
    (fun {_ _} hx hy => c.add_mem hx hy) (fun t {_} hx => c.real_smul_mem t hx)
    c.re c.im c.re_mem c.im_mem c.decomp c.continuous_re.continuousAt c.re_zero
    c.continuous_im.continuousAt c.im_zero U hU hu.1 f hf.differentiableOn
    (fun _ hx hr => hzero ⟨hx,hr⟩)

/-- All complex iterated derivatives vanish, including their mixed and diagonal values. -/
theorem sourceLemmaE2_iteratedFDeriv_eq_zero (c : RealComplexification R E) (U : Set E)
    (hU : IsOpen U) {u : E} (hu : u ∈ U ∩ c.realLocus)
    (f : E → F) (hf : AnalyticOnNhd ℂ f U) (hzero : EqOn f 0 (U ∩ c.realLocus))
    (n : ℕ) : iteratedFDeriv ℂ n f u = 0 := by
  have h := (sourceLemmaE2_zero_germ c U hU hu f hf hzero).iteratedFDeriv (𝕜 := ℂ) n
  simpa only [iteratedFDeriv_zero,Pi.zero_apply] using h.self_of_nhds

/-- Any local multilinear power series has zero diagonal coefficients in every complex direction. -/
theorem sourceLemmaE2_powerSeries_diagonal_zero (c : RealComplexification R E) (U : Set E)
    (hU : IsOpen U) {u : E} (hu : u ∈ U ∩ c.realLocus)
    (f : E → F) (hf : AnalyticOnNhd ℂ f U) (hzero : EqOn f 0 (U ∩ c.realLocus))
    (P : FormalMultilinearSeries ℂ E F) (hP : HasFPowerSeriesAt f P u)
    (n : ℕ) (v : E) : P n (fun _ => v) = 0 :=
  (hP.congr (sourceLemmaE2_zero_germ c U hU hu f hf hzero)).apply_eq_zero n v

end NLS.ComplexAnalysis
