import NLS.Fourier.PeriodOneContinuousRecovery
import NLS.FunctionalAnalysis.SmoothSpaceTimePartials

/-! Joint smoothness of an arbitrary periodic space-time field implies
time differentiability of its actual real mean-zero H1 representatives.
The continuous mixed partial is passed through bounded Fourier recovery. -/
noncomputable section
open NLS.WeightedCoeff NLS.FunctionalAnalysis
open scoped ContDiff
namespace NLS.Fourier

theorem differentiableAt_realPeriodOneCurve_of_smoothSpaceTime
    (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ t, Function.Periodic (fun x => f (t, x)) 1)
    (a : ℝ → fourierRealZeroSubmodule (Weight.signedSobolev (0 + 1)) 2)
    (ha : ∀ t k, (a t).val.val.val k = periodOneCoefficient (fun x => f (t, x)) k) (t : ℝ) :
    DifferentiableAt ℝ a t := by
  let u := spacePartial f
  let v := timePartial u
  have hu : ContDiff ℝ ∞ u := contDiff_spacePartial f hf
  have hv : ContDiff ℝ ∞ v := contDiff_timePartial u hu
  have hup (s : ℝ) : Function.Periodic (fun x => u (s, x)) 1 := periodic_spacePartial f hf hp s
  have hvp (s : ℝ) : Function.Periodic (fun x => v (s, x)) 1 := periodic_timePartial u hu hup s
  let U := fun s => periodicContinuousCircle (fun x => u (s, x))
    (hu.continuous.comp (continuous_const.prodMk continuous_id))
    (by simpa using! (hup s).nat_mul 2)
  have he : (fun s => periodOneContinuousRecovery (U s)) = a := by
    funext s
    have hs : ContDiff ℝ ∞ (fun x => f (s, x)) := hf.comp (contDiff_const.prodMk contDiff_id)
    have h := periodOneContinuousRecovery_deriv (fun x => f (s, x)) hs (hp s) (a s) (ha s)
    simpa only [U, u, spacePartial_eq_deriv f hf s] using h
  have hd := hasDerivAt_periodicContinuousCircle u v hu.continuous hv.continuous
    (fun s => by simpa using! (hup s).nat_mul 2)
    (fun s => by simpa using! (hvp s).nat_mul 2)
    (fun s x => hasDerivAt_timePartial u hu s x) t
  have h := @hasDerivAt_clm_comp (C(AddCircle (2 : ℝ), ℂ))
    (fourierRealZeroSubmodule (Weight.signedSobolev (0 + 1)) 2)
    inferInstance inferInstance inferInstance inferInstance
    periodOneContinuousRecovery _ _ t hd
  rw [he] at h
  exact HasDerivAt.differentiableAt (F := fourierRealZeroSubmodule (Weight.signedSobolev (0 + 1)) 2) h

end NLS.Fourier
