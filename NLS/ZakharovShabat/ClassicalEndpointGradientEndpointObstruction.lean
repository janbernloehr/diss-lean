import NLS.Fourier.AbsoluteSummabilityEndpoints
import NLS.ZakharovShabat.ClassicalEndpointPoisson
import NLS.ZakharovShabat.ClassicalEndpointGradientErrorIntegral

/-! # Boundary obstruction to absolute summability of endpoint gradients

A nonzero upper monodromy coupling forces a boundary jump in the second
component of the gradient of the upper diagonal entry. Its free gradient
vanishes, so the obstruction persists at every free reference frequency.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

/-- The diagonal gradient starts at the negative upper monodromy coupling. -/
theorem classicalEndpointGradient_fst_first_zero (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalEndpointGradient φ z (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) 0 =
      (0,-I*(classicalSolution φ z (0,1) 1).1) := by
  simp [classicalEndpointGradient]

/-- The second component of that same gradient vanishes at the terminal endpoint. -/
theorem classicalEndpointGradient_fst_first_one_snd (φ : Curve (ℂ × ℂ)) (z : ℂ) :
    (classicalEndpointGradient φ z (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) 1).2 = 0 := by
  have h := classicalEndpointGradient_eq_solution_product φ z (1,0)
    (ContinuousLinearMap.fst ℂ ℂ ℂ) ⟨1,by constructor <;> norm_num⟩
  rw [h,classicalEndpointDualSolution_one]
  simp

/-- A nonzero coupling excludes ℓ¹ for the actual gradient error, whatever its free reference. -/
theorem not_memlp_classicalEndpointGradientRemainder_one_of_upper_ne_zero
    (φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (hz : (classicalSolution φ z (0,1) 1).1 ≠ 0) :
    ¬Memℓp (intervalFourierCoefficient 1 (fun t =>
      (classicalEndpointGradientRemainder φ z w (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) t).2)) 1 := by
  apply not_memlp_intervalFourierCoefficient_one_of_endpoints_ne 1 (by norm_num)
    _ (contDiff_classicalEndpointGradientRemainder φ z w (1,0)
      (ContinuousLinearMap.fst ℂ ℂ ℂ)).continuous.snd
  simp only [classicalEndpointGradientRemainder,classicalFreeEndpointGradient_fst_first,sub_zero,
    classicalEndpointGradient_fst_first_zero,classicalEndpointGradient_fst_first_one_snd]
  exact mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz

end NLS.ZakharovShabat
