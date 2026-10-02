import NLS.ZakharovShabat.ClassicalFreePotentialGradients
import NLS.ZakharovShabat.SourceBoundaryPoissonGradient
import NLS.ZakharovShabat.SourceAntiDiscriminantPoissonGradient
import NLS.SequenceSpaces.FiniteSourceDensity

/-! # Free source cotangents from the actual classical gradients

Finite Fourier comparison and density identify the full Hilbert source
derivatives. Reversed first-component frequency and the signed second
anti-discriminant component come from explicit free physical waves.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem integral_wave_polynomial (a : ℤ →₀ ℂ) (n : ℤ) :
    (∫ x in (0 : ℝ)..1, wave (2*n) x * polynomial a x) = a (-n) := by
  have h : unitFourierCoefficient (polynomial a) (-n) = a (-n) := by
    rw [unitFourierCoefficient_eq_fourierCoeffOn,fourierCoeffOn_one,halfCoefficient_polynomial_even]
    ring
  simpa only [unitFourierCoefficient,mul_neg,neg_mul,neg_neg,mul_comm] using h

private theorem integral_wave_pair_finite (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) (c d : ℂ) :
    (∫ x in (0 : ℝ)..1, c*wave (2*n) x*(extend (finiteSourceCurve a) x).1 +
      d*wave (-(2*n)) x*(extend (finiteSourceCurve a) x).2) = c*a.1 (-n)+d*a.2 n := by
  have he : (∫ x in (0 : ℝ)..1, c*wave (2*n) x*(extend (finiteSourceCurve a) x).1 +
      d*wave (-(2*n)) x*(extend (finiteSourceCurve a) x).2) =
      ∫ x in (0 : ℝ)..1, c*(wave (2*n) x*polynomial a.1 x) + d*(wave (2*(-n)) x*polynomial a.2 x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
    dsimp only
    rw [extend_finiteSourceCurve a x hx']
    simp only [BoundaryCondition.periodOnePair,mul_neg,mul_assoc]
  have hiA : IntervalIntegrable (fun x : ℝ => c*(wave (2*n) x*polynomial a.1 x)) volume 0 1 :=
    ((((continuous_wave (2*n)).mul (continuous_polynomial a.1)).const_mul c).intervalIntegrable 0 1)
  have hiB : IntervalIntegrable (fun x : ℝ => d*(wave (2*(-n)) x*polynomial a.2 x)) volume 0 1 :=
    ((((continuous_wave (2*(-n))).mul (continuous_polynomial a.2)).const_mul d).intervalIntegrable 0 1)
  rw [he,intervalIntegral.integral_add hiA hiB,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_wave_polynomial,integral_wave_polynomial,neg_neg]

private theorem finiteSourceCurve_zero : finiteSourceCurve (0,0) = 0 :=
  finiteSourceCurveLinear.map_zero

/-- The exact free characteristic derivative in finite Fourier directions. -/
theorem sourceBoundaryCharacteristicCotangent_zero_finite
    (b : BoundaryCondition) (n : ℤ) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b ((Real.pi : ℂ)*n)
      0 (CoeffPair.ofFinsupp (p := 2) a) =
        -(BoundaryCondition.extensionSign b*cos ((Real.pi : ℂ)*n))/2 * (a.1 (-n)+a.2 n) := by
  have he := sourceBoundaryCharacteristicCotangent_finite_direction b (0,0) a ((Real.pi : ℂ)*n)
  simp only [show CoeffPair.ofFinsupp (p := 2) (0,0) = 0 from map_zero _,finiteSourceCurve_zero] at he
  rw [he,fderiv_classicalSeparatedCharacteristic_eq_gradient_integral]
  calc
    _ = ∫ x in (0 : ℝ)..1,
        (-(BoundaryCondition.extensionSign b*cos ((Real.pi : ℂ)*n))/2)*wave (2*n) x*(extend (finiteSourceCurve a) x).1 +
        (-(BoundaryCondition.extensionSign b*cos ((Real.pi : ℂ)*n))/2)*wave (-(2*n)) x*(extend (finiteSourceCurve a) x).2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [classicalSeparatedGradient_free_lattice b n x (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx)]
    _ = _ := by rw [integral_wave_pair_finite]; ring

/-- The exact free anti-discriminant derivative in finite Fourier directions. -/
theorem sourceAntiDiscriminantCotangent_zero_finite
    (n : ℤ) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    sourceAntiDiscriminantCotangent (by simp) (by norm_num) ((Real.pi : ℂ)*n)
      0 (CoeffPair.ofFinsupp (p := 2) a) =
        I*cos ((Real.pi : ℂ)*n) * (a.1 (-n)-a.2 n) := by
  have he := sourceAntiDiscriminantCotangent_finite_direction (0,0) a ((Real.pi : ℂ)*n)
  simp only [show CoeffPair.ofFinsupp (p := 2) (0,0) = 0 from map_zero _,finiteSourceCurve_zero] at he
  rw [he,fderiv_classicalAntiDiscriminant_eq_gradient_integral]
  calc
    _ = ∫ x in (0 : ℝ)..1, (I*cos ((Real.pi : ℂ)*n))*wave (2*n) x*(extend (finiteSourceCurve a) x).1 +
        (-I*cos ((Real.pi : ℂ)*n))*wave (-(2*n)) x*(extend (finiteSourceCurve a) x).2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [classicalAntiDiscriminantGradient_free_lattice n x (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx)]
    _ = _ := by rw [integral_wave_pair_finite]; ring

/-- The free discriminant has no first-order potential variation. -/
theorem sourceDiscriminantCotangent_zero_finite (z : ℂ) (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    sourceDiscriminantCotangent (by simp) z 0 (CoeffPair.ofFinsupp (p := 2) a) = 0 := by
  have he := sourceDiscriminantCotangent_finite_direction (0,0) a z
  simp only [show CoeffPair.ofFinsupp (p := 2) (0,0) = 0 from map_zero _,finiteSourceCurve_zero] at he
  rw [he,fderiv_classicalDiscriminant_eq_gradient_integral]
  calc
    _ = ∫ x in (0 : ℝ)..1, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [classicalDiscriminantGradient_free z x (by simpa only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx)]
      simp
    _ = 0 := intervalIntegral.integral_zero

/-- Completion preserves the exact signed Fourier formula. -/
theorem sourceBoundaryCharacteristicCotangent_zero
    (b : BoundaryCondition) (n : ℤ) (h : CoeffPair 2) :
    sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b ((Real.pi : ℂ)*n) 0 h =
      -(BoundaryCondition.extensionSign b*cos ((Real.pi : ℂ)*n))/2 * (h.fst (-n)+h.snd n) := by
  have heq := CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp)
    (sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b ((Real.pi : ℂ)*n) 0)
    (fun h : CoeffPair 2 => -(BoundaryCondition.extensionSign b*cos ((Real.pi : ℂ)*n))/2 * (h.fst (-n)+h.snd n))
    (ContinuousLinearMap.continuous _) (continuous_const.mul
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-n)).continuous.comp (CoeffPair.toMax 2).continuous.fst).add
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp (CoeffPair.toMax 2).continuous.snd)))
    (sourceBoundaryCharacteristicCotangent_zero_finite b n)
  exact congrFun heq h

theorem sourceAntiDiscriminantCotangent_zero (n : ℤ) (h : CoeffPair 2) :
    sourceAntiDiscriminantCotangent (by simp) (by norm_num) ((Real.pi : ℂ)*n) 0 h =
      I*cos ((Real.pi : ℂ)*n) * (h.fst (-n)-h.snd n) := by
  have heq := CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp)
    (sourceAntiDiscriminantCotangent (by simp) (by norm_num) ((Real.pi : ℂ)*n) 0)
    (fun h : CoeffPair 2 => I*cos ((Real.pi : ℂ)*n) * (h.fst (-n)-h.snd n))
    (ContinuousLinearMap.continuous _) (continuous_const.mul
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-n)).continuous.comp (CoeffPair.toMax 2).continuous.fst).sub
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp (CoeffPair.toMax 2).continuous.snd)))
    (sourceAntiDiscriminantCotangent_zero_finite n)
  exact congrFun heq h

theorem sourceDiscriminantCotangent_zero (z : ℂ) :
    sourceDiscriminantCotangent (by simp) z (0 : CoeffPair 2) = 0 := by
  have heq := CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp)
    (sourceDiscriminantCotangent (by simp) z 0) (fun _ => (0 : ℂ))
    (ContinuousLinearMap.continuous _) continuous_const (sourceDiscriminantCotangent_zero_finite z)
  ext h
  exact congrFun heq h

end NLS.ZakharovShabat
