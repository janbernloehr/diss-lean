import NLS.ZakharovShabat.ClassicalEndpointGradientBounds
import NLS.Fourier.UnitIntervalEnergyBound

/-! # Actual Fourier coefficients and L² bounds for the endpoint-gradient error -/

noncomputable section
open Set NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

/-- The actual unit-interval Fourier coefficients of a scalar gradient-error component. -/
def classicalEndpointGradientRemainderL2Coefficients
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) : Coeff 2 :=
  unitIntervalL2Coefficients (fun t => P (classicalEndpointGradientRemainder φ z w v L t))
    (P.continuous.comp (contDiff_classicalEndpointGradientRemainder φ z w v L).continuous)

@[simp] theorem classicalEndpointGradientRemainderL2Coefficients_apply
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (k : ℤ) :
    classicalEndpointGradientRemainderL2Coefficients φ z w v L P k =
      intervalFourierCoefficient 1 (fun t => P (classicalEndpointGradient φ z v L t-
        classicalFreeEndpointGradient w v L t)) k := rfl

/-- A pointwise bound transfers to the norm of the actual Fourier sequence by Parseval. -/
theorem norm_classicalEndpointGradientRemainderL2Coefficients_of_bound
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ t : Icc (0 : ℝ) 1, ‖classicalEndpointGradientRemainder φ z w v L t‖ ≤ A) :
    ‖classicalEndpointGradientRemainderL2Coefficients φ z w v L P‖ ≤ A := by
  apply norm_unitIntervalL2Coefficients_le _ _ A hA
  intro t ht
  exact (P.le_opNorm _).trans ((mul_le_mul_of_nonneg_right hP (norm_nonneg _)).trans
    (by simpa using h ⟨t,ht⟩))

/-- The actual gradient-error Fourier norm decays inversely with spectral frequency. -/
theorem norm_classicalEndpointGradientRemainderL2Coefficients_sobolev_le
    (M H : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (z : ℂ) (hz : z ≠ 0) (hH : |z.im| ≤ H)
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    ‖classicalEndpointGradientRemainderL2Coefficients (classicalSobolevPotential a) z z v L P‖ ≤
      6*(Real.exp (4*M+H))^2*classicalSobolevErrorConstant M H/‖z‖ := by
  have hC := classicalSobolevErrorConstant_nonneg M H ((norm_nonneg a).trans ha)
  exact norm_classicalEndpointGradientRemainderL2Coefficients_of_bound _ _ _ _ _ P hP _ (by positivity)
    (norm_classicalEndpointGradientRemainder_sobolev_strip_le M H a ha z hz hH v hv L hL)

/-- Replacing the free reference by nπ preserves inverse-index Fourier decay. -/
theorem norm_classicalEndpointGradientRemainderL2Coefficients_shifted_le
    (M B : ℝ) (hB : 0 ≤ B) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (n : ℤ) (hn : 1 ≤ (n.natAbs : ℝ)) (hBn : B ≤ (n.natAbs : ℝ)) (z : ℂ)
    (hδ : ‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    ‖classicalEndpointGradientRemainderL2Coefficients (classicalSobolevPotential a) z
      ((Real.pi*(n : ℝ) : ℝ) : ℂ) v L P‖ ≤
      6*(Real.exp (4*M+B))^2*(classicalSobolevErrorConstant M B+2*B)/(n.natAbs : ℝ) := by
  have hC := classicalSobolevErrorConstant_nonneg M B ((norm_nonneg a).trans ha)
  exact norm_classicalEndpointGradientRemainderL2Coefficients_of_bound _ _ _ _ _ P hP _ (by positivity)
    (norm_classicalEndpointGradientRemainder_shifted_le M B hB a ha n hn hBn z hδ v hv L hL)

/-- A coarse bound at every pair of frequencies controls arbitrary finite spectral heads. -/
theorem norm_classicalEndpointGradientRemainderL2Coefficients_all_frequencies_le
    (M : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M) (z w : ℂ)
    (v : ℂ × ℂ) (hv : ‖v‖ ≤ 1) (L : (ℂ × ℂ) →L[ℂ] ℂ) (hL : ‖L‖ ≤ 1)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    ‖classicalEndpointGradientRemainderL2Coefficients (classicalSobolevPotential a) z w v L P‖ ≤
      12*(Real.exp (4*M+‖z‖+‖w‖))^3 := by
  exact norm_classicalEndpointGradientRemainderL2Coefficients_of_bound _ _ _ _ _ P hP _ (by positivity)
    (norm_classicalEndpointGradientRemainder_all_frequencies_le M a ha z w v hv L hL)

end NLS.ZakharovShabat
