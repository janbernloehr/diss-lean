import NLS.Fourier.AbsoluteContinuousCoefficients

/-!
# Fourier realization of arbitrary square-integrable interval data

Normalized Fourier coefficients reconstruct every `L²` function almost
everywhere on a period of length two. This includes folded potentials with
jumps and imposes no endpoint matching or global regularity condition.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.Fourier

/-- The actual normalized coefficients of square-integrable physical period data. -/
def periodTwoL2Coefficients (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) : Coeff 2 :=
  ⟨periodTwoCoefficient f, memlp_periodTwoCoefficient hf⟩

@[simp] theorem periodTwoL2Coefficients_apply (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) (n : ℤ) :
    periodTwoL2Coefficients f hf n = periodTwoCoefficient f n := rfl

/-- Fourier synthesis reconstructs arbitrary physical `L²` data on the full period. -/
theorem circlePullback_periodTwoL2Coefficients (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) :
    circlePullback (l2Synthesis (periodTwoL2Coefficients f hf))
      =ᵐ[volume.restrict (Ioc 0 2)] f := by
  have hl : MemLp (AddCircle.liftIoc 2 0 f) 2 AddCircle.haarAddCircle := by
    have ht : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (0 + 2))) := by simpa using hf
    exact ht.memLp_liftIoc.haarAddCircle
  have he : l2Synthesis (periodTwoL2Coefficients f hf) = hl.toLp (AddCircle.liftIoc 2 0 f) := by
    apply fourierBasis.repr.injective
    ext n
    rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_l2Synthesis,
      periodTwoL2Coefficients_apply, fourierCoeff_congr_ae hl.coeFn_toLp, fourierCoeff_liftIoc_eq]
    simpa only [zero_add] using periodTwoCoefficient_eq_fourierCoeffOn f n
  rw [he]
  have hp := circle_ae_pullback hl.coeFn_toLp
  filter_upwards [hp, ae_restrict_mem measurableSet_Ioc] with x hx hmem
  exact hx.trans (AddCircle.liftIoc_zero_coe_apply hmem)

/-- Taking physical Fourier integrals is also a left inverse of Hilbert synthesis. -/
@[simp] theorem periodTwoL2Coefficients_circlePullback (a : Coeff 2) :
    periodTwoL2Coefficients (circlePullback (l2Synthesis a)) (memLp_circlePullback _) = a := by
  ext n
  rw [periodTwoL2Coefficients_apply, periodTwoCoefficient_circlePullback, fourierCoeff_l2Synthesis]

/-- The interval coefficients depend only on the almost-everywhere physical function. -/
theorem periodTwoL2Coefficients_congr (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 2))) (hg : MemLp g 2 (volume.restrict (Ioc 0 2)))
    (h : f =ᵐ[volume.restrict (Ioc 0 2)] g) :
    periodTwoL2Coefficients f hf = periodTwoL2Coefficients g hg := by
  ext n
  simpa only [periodTwoL2Coefficients_apply, periodTwoCoefficient_eq_fourierCoeffOn] using
    congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 2) h) n

end NLS.Fourier
