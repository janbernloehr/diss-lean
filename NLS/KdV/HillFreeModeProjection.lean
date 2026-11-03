import NLS.KdV.HillFreeRieszFourier

/-! The literal two-mode free projector, independent of contour inversion,
and its equality with the actual zero-potential source contour operator. -/
noncomputable section
namespace NLS.KdV
open NLS.Fourier

/-- The actual bounded free Fourier projector with continuous physical outputs. -/
def hillFreeContinuousModeProjection (n : ℕ) : CircleL2 →L[ℂ] C(AddCircle (2:ℝ),ℂ) :=
  ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n:ℤ)).comp
    l2Synthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap).smulRight (fourier (n:ℤ))+
  ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-(n:ℤ))).comp
    l2Synthesis.symm.toContinuousLinearEquiv.toContinuousLinearMap).smulRight (fourier (-(n:ℤ)))

/-- Its output is the literal sum of the two original signed Fourier modes. -/
theorem hillFreeContinuousModeProjection_apply (n : ℕ) (F : CircleL2) :
    hillFreeContinuousModeProjection n F =
      fourierCoeff F (n:ℤ) • (fourier (n:ℤ) : C(AddCircle (2:ℝ),ℂ))+
        fourierCoeff F (-(n:ℤ)) • (fourier (-(n:ℤ)) : C(AddCircle (2:ℝ),ℂ)) := by
  change fourierBasis.repr F (n:ℤ) • (fourier (n:ℤ) : C(AddCircle (2:ℝ),ℂ))+
    fourierBasis.repr F (-(n:ℤ)) • (fourier (-(n:ℤ)) : C(AddCircle (2:ℝ),ℂ)) = _
  rw [fourierBasis_repr,fourierBasis_repr]

/-- The same literal free projector in the original physical L2 norm. -/
def hillFreeL2ModeProjection (n : ℕ) : CircleL2 →L[ℂ] CircleL2 :=
  (circleContinuousToLp 2).comp (hillFreeContinuousModeProjection n)

/-- The ACTUAL zero-potential continuous contour operator is this literal free projector. -/
theorem hillContinuousRieszProjection_zero_eq_modes (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) :
    singularHillContinuousRieszProjection 0 (freeHillValue n:ℂ) (n:ℝ) = hillFreeContinuousModeProjection n := by
  apply ContinuousLinearMap.ext
  intro F
  rw [hillFreeContinuousModeProjection_apply]
  exact hillContinuousRieszProjection_zero_fourier_kernel n hn hlog F

/-- The ACTUAL zero-potential L2 contour operator is exactly the SAME free projector. -/
theorem hillL2RieszProjection_zero_eq_modes (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) :
    singularHillL2RieszProjection 0 (freeHillValue n:ℂ) (n:ℝ) = hillFreeL2ModeProjection n := by
  apply ContinuousLinearMap.ext
  intro F
  rw [← singularHillContinuousRieszProjection_toLp,hillContinuousRieszProjection_zero_eq_modes n hn hlog]
  rfl

end NLS.KdV
