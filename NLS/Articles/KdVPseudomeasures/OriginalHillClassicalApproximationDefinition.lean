import NLS.Articles.KdVPseudomeasures.OriginalHillClassicalApproximation
import NLS.Articles.KdVPseudomeasures.OriginalHillRoughSmoothApproximationSolutions
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteNativeSpaceTimeSmooth

/-! The original rough solution formulation using EVERY family of
jointly smooth classical real mean-zero unit-period KdV solutions.
The realization retains every original Fourier coefficient. -/
noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.KdV NLS.WeightedCoeff NLS.Fourier NLS.ZakharovShabat
open scoped ContDiff ComplexConjugate
namespace NLS.Articles.KdVPseudomeasures

def HillClassicalSpaceTimeKdVSolution (f : ℝ × ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧
  (∀ t, Function.Periodic (fun x => f (t, x)) 1) ∧
  (∀ t x, conj (f (t, x)) = f (t, x)) ∧
  (∀ t, (∫ x in (0 : ℝ)..1, f (t, x)) = 0) ∧
  ∀ t x, HasDerivAt (fun r => f (r, x))
    (classicalKdVVectorField (fun y => f (t, y)) x) t

def hillClassicalSolutionRoughCurve (f : ℝ × ℝ → ℂ) (hf : HillClassicalSpaceTimeKdVSolution f)
    (t : ℝ) : HillRealMeanZeroSource :=
  hillIntegerSourceInclusion 4
    (hillClassicalSmoothCurve f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 t)

theorem hillClassicalSolutionRoughCurve_coefficients
    (f : ℝ × ℝ → ℂ) (hf : HillClassicalSpaceTimeKdVSolution f) (t : ℝ) (k : ℤ) :
    (hillClassicalSolutionRoughCurve f hf t).val.val.val k =
      periodOneCoefficient (fun x => f (t, x)) k := by
  rw [hillClassicalSolutionRoughCurve, hillIntegerSourceInclusion_apply,
    hillClassicalSmoothCurve_coefficients]

theorem hillClassicalSolutionRoughCurve_eq_canonicalFlow
    (f : ℝ × ℝ → ℂ) (hf : HillClassicalSpaceTimeKdVSolution f) (t : ℝ) :
    hillClassicalSolutionRoughCurve f hf t =
      hillRoughCanonicalKdVFlow (hillClassicalSolutionRoughCurve f hf 0) t := by
  rw [hillClassicalSolutionRoughCurve,
    hillClassicalSmoothCurve_eq_canonicalFlow f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2,
    hillIntegerCanonicalKdVFlow_inclusion]
  rfl

theorem hillFiniteNative_is_classicalSpaceTimeSolution
    (q : RealSignedHilbert (signedStepOrder 0 4)) (S : Finset ℤ)
    (hq : ∀ k ∉ S, ((hillIntegerSobolevEquiv 4).equiv q).val.val.val k = 0) :
    HillClassicalSpaceTimeKdVSolution
      (fun u : ℝ × ℝ => hillPhysicalH4Synthesis (hillIntegerCanonicalKdVFlow 4 q u.1) u.2) := by
  have h := contDiff_hillFiniteNative_H4_space_time q S hq
  have hs : ContDiff ℝ ∞ (hillPhysicalH4Synthesis q) := by
    have hi := h.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)
    simpa only [Function.comp_def, hillIntegerCanonicalKdVFlow_zero] using! hi
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · intro t
    exact hillPhysicalH4Synthesis_periodic (hillIntegerCanonicalKdVFlow 4 q t)
  · intro t x
    exact hillPhysicalH4Synthesis_real (hillIntegerCanonicalKdVFlow 4 q t) x
  · intro t
    exact hillPhysicalH4Synthesis_mean_zero (hillIntegerCanonicalKdVFlow 4 q t)
  · intro t x
    exact hasDerivAt_hillIntegerCanonicalKdVFlow_physical_PDE q hs t x

theorem hillClassicalSolutionRoughCurve_of_physicalStrongCurve
    (Γ : ℝ → RealSignedHilbert (signedStepOrder 0 4))
    (hΓ : HillClassicalSpaceTimeKdVSolution (fun u : ℝ × ℝ => hillPhysicalH4Synthesis (Γ u.1) u.2))
    (t : ℝ) :
    hillClassicalSolutionRoughCurve (fun u : ℝ × ℝ => hillPhysicalH4Synthesis (Γ u.1) u.2) hΓ t =
      hillIntegerSourceInclusion 4 (Γ t) := by
  apply hillRealMeanZeroInclusion_injective
  apply Subtype.ext
  funext k
  change (hillClassicalSolutionRoughCurve _ hΓ t).val.val.val k =
    (hillIntegerSourceInclusion 4 (Γ t)).val.val.val k
  rw [hillClassicalSolutionRoughCurve_coefficients, hillIntegerSourceInclusion_apply]
  exact hillPhysicalH4Synthesis_coefficients (Γ t) k

def HillRoughSolutionByClassicalApproximation (q : HillRealMeanZeroSource)
    (γ : ℝ → HillRealMeanZeroSource) : Prop :=
  Continuous γ ∧ γ 0 = q ∧
  ∀ (F : ℕ → ℝ × ℝ → ℂ) (hF : ∀ j, HillClassicalSpaceTimeKdVSolution (F j)),
    Tendsto (fun j => hillClassicalSolutionRoughCurve (F j) (hF j) 0) atTop (𝓝 q) →
    ∀ t, Tendsto (fun j => hillClassicalSolutionRoughCurve (F j) (hF j) t) atTop (𝓝 (γ t))

end NLS.Articles.KdVPseudomeasures
