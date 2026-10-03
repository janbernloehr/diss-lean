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
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hφ : ‖classicalSobolevPotential a‖ ≤ 4*M :=
    (norm_classicalSobolevPotential_le a).trans (by linarith)
  let E := Real.exp (4*M+‖z‖+‖w‖)
  have hE : 0 ≤ E := Real.exp_nonneg _
  apply norm_classicalEndpointGradientRemainderL2Coefficients_of_bound _ _ _ _ _ P hP _ (by positivity)
  intro t
  have h := norm_classicalEndpointGradientRemainder_of_bounds (classicalSobolevPotential a) z w v hv L hL
    E (2*E) hE (by positivity) ?_ t
  · exact h.trans_eq (by dsimp [E]; ring)
  intro u hu s
  have hS : ‖classicalSolution (classicalSobolevPotential a) z u s‖ ≤ E :=
    (norm_classicalSolution_unit_strip_le (4*M) ‖z‖ _ hφ z (Complex.abs_im_le_norm z) u hu s).trans
      (Real.exp_le_exp.mpr (by linarith [norm_nonneg w]))
  have hF : ‖classicalFreeVector w u s‖ ≤ E := by
    have he : classicalFreeVector w u s = classicalSolution 0 w u s := by
      simp [classicalSolution_free,classicalFreeVector]
    rw [he]
    apply (norm_classicalSolution_unit_strip_le (4*M) ‖w‖ 0
      (by simpa using (show 0 ≤ 4*M by positivity)) w (Complex.abs_im_le_norm w) u hu s).trans
    apply Real.exp_le_exp.mpr
    linarith [norm_nonneg z]
  exact ⟨hS,hF,(norm_sub_le _ _).trans ((add_le_add hS hF).trans_eq (by ring))⟩

end NLS.ZakharovShabat
