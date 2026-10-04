import NLS.ComplexAnalysis.FDerivAnalyticLine
import NLS.ComplexAnalysis.BanachSmoothAnalyticOn

/-! # Complex Fréchet differentiability implies Banach-space analyticity

Differentiation preserves holomorphicity on an open domain. Induction
gives every finite differentiability order, and the existing Banach
Taylor-series theorem then supplies a convergent local power series.
-/
noncomputable section
open Set
open scoped ContDiff ENNReal
universe u
namespace NLS.ComplexAnalysis
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A complex-differentiable map on an open normed domain has every finite
complex differentiability order. -/
theorem contDiffOn_nat_of_complexDifferentiableOn
    (n : ℕ) (f : E → F) (U : Set E) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) : ContDiffOn ℂ n f U := by
  induction n generalizing F with
  | zero => exact contDiffOn_zero.mpr hf.continuousOn
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiffOn_succ_iff_fderiv_of_isOpen hU]
    exact ⟨hf,by simp,ih (fderiv ℂ f) (differentiableOn_fderiv_of_differentiableOn f U hU hf)⟩

/-- Complex Fréchet differentiability on an open set implies complex smoothness. -/
theorem contDiffOn_infty_of_complexDifferentiableOn
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ ∞ f U :=
  contDiffOn_infty.mpr (fun n => contDiffOn_nat_of_complexDifferentiableOn n f U hU hf)

/-- The normalized Fréchet Taylor series converges on a positive-radius ball. -/
theorem hasFPowerSeriesOnBall_of_complexDifferentiableOn
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (a : E) (ha : a ∈ U) :
    ∃ r : ℝ≥0∞, HasFPowerSeriesOnBall f (complexTaylorSeries f a) a r :=
  hasFPowerSeriesOnBall_of_complexSmoothOn f hU
    (contDiffOn_infty_of_complexDifferentiableOn f U hU hf) ha

/-- A holomorphic map into a complete complex normed space has a local
Banach power series throughout its open domain. -/
theorem analyticOnNhd_of_complexDifferentiableOn
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    AnalyticOnNhd ℂ f U :=
  analyticOnNhd_of_complexSmoothOn f hU (contDiffOn_infty_of_complexDifferentiableOn f U hU hf)

/-- Norm continuity and analyticity on every complex line imply joint
Banach-space analyticity on an open domain. -/
theorem analyticOnNhd_of_analyticLines
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hl : ∀ a ∈ U, ∀ v : E, AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • v))
      ((fun t : ℂ => a+t • v) ⁻¹' U)) : AnalyticOnNhd ℂ f U :=
  analyticOnNhd_of_complexDifferentiableOn f U hU (differentiableOn_of_analyticLines f U hU hf hl)

end NLS.ComplexAnalysis
