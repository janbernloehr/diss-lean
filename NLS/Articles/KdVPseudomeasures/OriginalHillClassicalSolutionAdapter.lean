import NLS.Articles.KdVPseudomeasures.OriginalHillSmoothPhysicalSolutions
import NLS.Fourier.SmoothRealMeanZeroPeriodOneData
import NLS.Fourier.SmoothRealPeriodOneCurve

/-! Arbitrary jointly smooth real mean-zero classical periodic solutions
in the genuine H4/H1 model. The strong time derivative is proved from
joint smoothness; it is not an extra hypothesis on classical solutions. -/
noncomputable section
open Set Complex MeasureTheory NLS.KdV NLS.WeightedCoeff NLS.Fourier NLS.ZakharovShabat
open scoped ContDiff ComplexConjugate
namespace NLS.Articles.KdVPseudomeasures

def hillClassicalSmoothCurve (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, Function.Periodic (fun x => f (t, x)) 1)
    (hr : ∀ t x, conj (f (t, x)) = f (t, x))
    (h0 : ∀ t, (∫ x in (0 : ℝ)..1, f (t, x)) = 0) :
    ℝ → RealSignedHilbert (signedStepOrder 0 4) := fun t =>
  smoothRealMeanZeroPeriodOneData _ (by rw [hillIntegerSobolev_source_order]; norm_num)
    (fun x => f (t, x)) (hf.comp (contDiff_const.prodMk contDiff_id)) (hp t) (hr t)
    (periodOneCoefficient_zero_of_mean_zero _ (h0 t))

theorem hillClassicalSmoothCurve_coefficients (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, Function.Periodic (fun x => f (t, x)) 1)
    (hr : ∀ t x, conj (f (t, x)) = f (t, x))
    (h0 : ∀ t, (∫ x in (0 : ℝ)..1, f (t, x)) = 0) (t : ℝ) (k : ℤ) :
    (hillClassicalSmoothCurve f hf hp hr h0 t).val.val.val k =
      periodOneCoefficient (fun x => f (t, x)) k :=
  smoothRealMeanZeroPeriodOneData_apply _ _ _ _ _ _ _ k

theorem hillClassicalSmoothCurve_physical (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, Function.Periodic (fun x => f (t, x)) 1)
    (hr : ∀ t x, conj (f (t, x)) = f (t, x))
    (h0 : ∀ t, (∫ x in (0 : ℝ)..1, f (t, x)) = 0) (t : ℝ) :
    hillPhysicalH4Synthesis (hillClassicalSmoothCurve f hf hp hr h0 t) = (fun x => f (t, x)) := by
  apply periodOneSobolevSynthesis_eq_of_coefficients _ _
    (hf.continuous.comp (continuous_const.prodMk continuous_id)) (hp t)
  intro k
  rw [signedOneRealToScalarDomain_apply, hillIntegerSourceOrderInclusion_apply,
    hillClassicalSmoothCurve_coefficients]
  rfl

theorem hillClassicalSmoothCurve_is_strong (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, Function.Periodic (fun x => f (t, x)) 1)
    (hr : ∀ t x, conj (f (t, x)) = f (t, x))
    (h0 : ∀ t, (∫ x in (0 : ℝ)..1, f (t, x)) = 0)
    (hPDE : ∀ t x, HasDerivAt (fun r => f (r, x))
      (classicalKdVVectorField (fun y => f (t, y)) x) t) :
    HillSmoothStrongKdVSolution (hillClassicalSmoothCurve f hf hp hr h0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rw [hillClassicalSmoothCurve_physical]
    exact hf.comp (contDiff_const.prodMk contDiff_id)
  · intro t
    have hd := differentiableAt_realPeriodOneCurve_of_smoothSpaceTime f hf hp
      (fun r => hillIntegerSourceOrderInclusion 1 4 (by decide) (hillClassicalSmoothCurve f hf hp hr h0 r))
      (by intro r k; rw [hillIntegerSourceOrderInclusion_apply, hillClassicalSmoothCurve_coefficients]) t
    exact ⟨_, DifferentiableAt.hasDerivAt (F := RealSignedHilbert (signedStepOrder 0 1)) hd⟩
  · intro t x
    simp only [hillClassicalSmoothCurve_physical]
    exact hPDE t x

theorem hillClassicalSmoothCurve_eq_canonicalFlow (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, Function.Periodic (fun x => f (t, x)) 1)
    (hr : ∀ t x, conj (f (t, x)) = f (t, x))
    (h0 : ∀ t, (∫ x in (0 : ℝ)..1, f (t, x)) = 0)
    (hPDE : ∀ t x, HasDerivAt (fun r => f (r, x))
      (classicalKdVVectorField (fun y => f (t, y)) x) t) (t : ℝ) :
    hillClassicalSmoothCurve f hf hp hr h0 t =
      hillIntegerCanonicalKdVFlow 4 (hillClassicalSmoothCurve f hf hp hr h0 0) t :=
  hillSmoothStrongKdVSolution_eq_canonicalFlow _
    (hillClassicalSmoothCurve_is_strong f hf hp hr h0 hPDE) t

theorem hillClassicalSmoothSolution_physical_eq_canonicalFlow (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, Function.Periodic (fun x => f (t, x)) 1)
    (hr : ∀ t x, conj (f (t, x)) = f (t, x))
    (h0 : ∀ t, (∫ x in (0 : ℝ)..1, f (t, x)) = 0)
    (hPDE : ∀ t x, HasDerivAt (fun r => f (r, x))
      (classicalKdVVectorField (fun y => f (t, y)) x) t) (t x : ℝ) :
    f (t, x) = hillPhysicalH4Synthesis
      (hillIntegerCanonicalKdVFlow 4 (hillClassicalSmoothCurve f hf hp hr h0 0) t) x := by
  rw [← hillClassicalSmoothCurve_eq_canonicalFlow f hf hp hr h0 hPDE,
    hillClassicalSmoothCurve_physical]

end NLS.Articles.KdVPseudomeasures
