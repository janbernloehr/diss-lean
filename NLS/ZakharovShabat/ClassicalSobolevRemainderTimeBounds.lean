import NLS.Fourier.UnitIntervalEnergyBound
import NLS.ZakharovShabat.ClassicalRemainderTimeRegularity
import NLS.ZakharovShabat.ClassicalSobolevRemainderBound

/-! # Appendix G.3 time-norm bounds for the actual remainder

Every scalar matrix entry is a contractive linear observation of a
fundamental column. Its unit-interval Fourier ℓ² norm has inverse-frequency
decay, and its classical H¹ time norm is uniformly bounded away from zero
spectral frequency. All constants are uniform on H¹ balls and strips.
-/

noncomputable section
open Set MeasureTheory NLS.Fourier
namespace NLS.ZakharovShabat

/-- Uniform numerator in the inverse-frequency error estimate. -/
def classicalSobolevErrorConstant (M H : ℝ) : ℝ := (4+Real.pi)*M*Real.exp (4*M+H)

/-- Uniform time-derivative constant. -/
def classicalSobolevDerivativeConstant (M H : ℝ) : ℝ := (8+Real.pi)*M*Real.exp (4*M+H)

theorem classicalSobolevErrorConstant_nonneg (M H : ℝ) (hM : 0 ≤ M) :
    0 ≤ classicalSobolevErrorConstant M H := by unfold classicalSobolevErrorConstant; positivity

theorem classicalSobolevDerivativeConstant_nonneg (M H : ℝ) (hM : 0 ≤ M) :
    0 ≤ classicalSobolevDerivativeConstant M H := by unfold classicalSobolevDerivativeConstant; positivity

/-- The actual Fourier coefficients of a scalar observation, with unit-interval normalization. -/
def classicalSobolevRemainderL2Coefficients
    (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) : Coeff 2 :=
  unitIntervalL2Coefficients (fun t => L (classicalSolutionRemainder (classicalSobolevPotential a) z v t))
    (contDiff_classicalRemainder_observation _ z v L).continuous

@[simp] theorem classicalSobolevRemainderL2Coefficients_apply
    (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) (n : ℤ) :
    classicalSobolevRemainderL2Coefficients a z v L n =
      intervalFourierCoefficient 1 (fun t => L (classicalSolutionRemainder (classicalSobolevPotential a) z v t)) n := rfl

section Bounds
variable (M H : ℝ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
  (z : ℂ) (hz : z ≠ 0) (hH : |z.im| ≤ H) (v : ℂ × ℂ)
  (L : (ℂ × ℂ) →L[ℝ] ℂ) (hL : ‖L‖ ≤ 1)
include ha hz hH hL

/-- Contractive observations retain the same pointwise remainder bound. -/
theorem norm_classicalSobolevRemainder_observation_le (t : Icc (0 : ℝ) 1) :
    ‖L (classicalSolutionRemainder (classicalSobolevPotential a) z v t)‖ ≤
      classicalSobolevErrorConstant M H*‖v‖/‖z‖ := by
  have hx := L.le_opNorm (classicalSolutionRemainder (classicalSobolevPotential a) z v t)
  have hp := norm_classicalSolutionRemainder_sobolev_strip_le M H a ha z hz hH v t
  have hn := norm_nonneg (classicalSolutionRemainder (classicalSobolevPotential a) z v t)
  unfold classicalSobolevErrorConstant
  calc
    _ ≤ ‖classicalSolutionRemainder (classicalSobolevPotential a) z v t‖ := by nlinarith
    _ ≤ (4+Real.pi)*M*‖v‖/‖z‖*Real.exp (4*M+H) := hp
    _ = _ := by ring

/-- The derivative of an observation is controlled by the actual vector derivative. -/
theorem norm_deriv_classicalSobolevRemainder_observation_le (t : Icc (0 : ℝ) 1) :
    ‖deriv (fun s => L (classicalSolutionRemainder (classicalSobolevPotential a) z v s)) t‖ ≤
      classicalSobolevDerivativeConstant M H*‖v‖ := by
  rw [deriv_classicalRemainder_observation]
  have hx := L.le_opNorm (deriv (classicalSolutionRemainder (classicalSobolevPotential a) z v) t)
  have hp := norm_deriv_classicalSolutionRemainder_sobolev_strip_le M H a ha z hz hH v t
  have hn := norm_nonneg (deriv (classicalSolutionRemainder (classicalSobolevPotential a) z v) t)
  unfold classicalSobolevDerivativeConstant
  calc
    _ ≤ ‖deriv (classicalSolutionRemainder (classicalSobolevPotential a) z v) t‖ := by nlinarith
    _ ≤ (8+Real.pi)*M*‖v‖*Real.exp (4*M+H) := hp
    _ = _ := by ring

/-- The actual L² time energy decays quadratically in the spectral frequency. -/
theorem integral_sq_classicalSobolevRemainder_le :
    (∫ t in (0 : ℝ)..1, ‖L (classicalSolutionRemainder (classicalSobolevPotential a) z v t)‖^2) ≤
      (classicalSobolevErrorConstant M H*‖v‖/‖z‖)^2 := by
  apply integral_sq_unit_le _ (contDiff_classicalRemainder_observation _ z v L).continuous _
    (div_nonneg (mul_nonneg (classicalSobolevErrorConstant_nonneg M H ((norm_nonneg a).trans ha))
      (norm_nonneg _)) (norm_nonneg _))
  intro t ht
  exact norm_classicalSobolevRemainder_observation_le M H a ha z hz hH v L hL ⟨t,ht⟩

/-- Parseval gives inverse-frequency decay of the whole Fourier coefficient ℓ² norm. -/
theorem norm_classicalSobolevRemainderL2Coefficients_le :
    ‖classicalSobolevRemainderL2Coefficients a z v L‖ ≤
      classicalSobolevErrorConstant M H*‖v‖/‖z‖ := by
  apply norm_unitIntervalL2Coefficients_le _ _ _
    (div_nonneg (mul_nonneg (classicalSobolevErrorConstant_nonneg M H ((norm_nonneg a).trans ha))
      (norm_nonneg _)) (norm_nonneg _))
  intro t ht
  exact norm_classicalSobolevRemainder_observation_le M H a ha z hz hH v L hL ⟨t,ht⟩

/-- The H¹ time norm is uniformly bounded for `|z| ≥ 1`, as needed before interpolation in G.3. -/
theorem sqrt_intervalH1Energy_classicalSobolevRemainder_le (hz1 : 1 ≤ ‖z‖) :
    Real.sqrt (intervalH1Energy
      (fun t => L (classicalSolutionRemainder (classicalSobolevPotential a) z v t)) 0 1) ≤
      (classicalSobolevErrorConstant M H+classicalSobolevDerivativeConstant M H)*‖v‖ := by
  have hC := classicalSobolevErrorConstant_nonneg M H ((norm_nonneg a).trans ha)
  have hD := classicalSobolevDerivativeConstant_nonneg M H ((norm_nonneg a).trans ha)
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖L (classicalSolutionRemainder (classicalSobolevPotential a) z v t)‖ ≤
        classicalSobolevErrorConstant M H*‖v‖ := by
    apply (norm_classicalSobolevRemainder_observation_le M H a ha z hz hH v L hL ⟨t,ht⟩).trans
    exact div_le_self (mul_nonneg hC (norm_nonneg _)) hz1
  have h := sqrt_intervalH1Energy_unit_le _ (contDiff_classicalRemainder_observation _ z v L)
    (classicalSobolevErrorConstant M H*‖v‖) (classicalSobolevDerivativeConstant M H*‖v‖)
    (mul_nonneg hC (norm_nonneg _)) (mul_nonneg hD (norm_nonneg _)) hf
    (fun t ht => norm_deriv_classicalSobolevRemainder_observation_le M H a ha z hz hH v L hL ⟨t,ht⟩)
  simpa only [add_mul] using h

end Bounds
end NLS.ZakharovShabat
