import NLS.ZakharovShabat.ClassicalCharacteristicGradientRemainders
import NLS.ZakharovShabat.ClassicalEndpointGradientFourierInterpolation
import NLS.Fourier.IntervalCoefficientLinearity

/-! # Actual Fourier coefficients of the characteristic gradients

The coefficient-space sums below are identified with the literal physical
Fourier integrals. This makes the endpoint-gradient bounds applicable to
the actual discriminant and anti-discriminant potential derivatives.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Fourier coefficients of a scalar observation of the actual discriminant gradient. -/
def classicalDiscriminantGradientFourierCoefficients {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (P : (ℂ × ℂ) →L[ℝ] ℂ) : Coeff q :=
  classicalEndpointGradientFourierCoefficients hq φ z z (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) P+
  classicalEndpointGradientFourierCoefficients hq φ z z (0,1) (ContinuousLinearMap.snd ℂ ℂ ℂ) P

/-- Fourier coefficients of the actual anti-discriminant gradient error. -/
def classicalAntiDiscriminantGradientFourierCoefficients {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (P : (ℂ × ℂ) →L[ℝ] ℂ) : Coeff q :=
  classicalEndpointGradientFourierCoefficients hq φ z w (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) P+
  classicalEndpointGradientFourierCoefficients hq φ z w (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) P

@[simp] theorem classicalDiscriminantGradientFourierCoefficients_apply {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (P : (ℂ × ℂ) →L[ℝ] ℂ) (k : ℤ) :
    classicalDiscriminantGradientFourierCoefficients hq φ z P k =
      intervalFourierCoefficient 1 (fun t => P (classicalDiscriminantGradient φ z t)) k := by
  have hc (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ) :
      Continuous (fun t => P (classicalEndpointGradientRemainder φ z z v L t)) :=
    P.continuous.comp (contDiff_classicalEndpointGradientRemainder φ z z v L).continuous
  change intervalFourierCoefficient 1 (fun t => P (classicalEndpointGradientRemainder φ z z (1,0) _ t)) k+
    intervalFourierCoefficient 1 (fun t => P (classicalEndpointGradientRemainder φ z z (0,1) _ t)) k = _
  rw [← intervalFourierCoefficient_add 1 _ _ (hc (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ))
    (hc (0,1) (ContinuousLinearMap.snd ℂ ℂ ℂ))]
  congr 1
  funext t
  rw [classicalDiscriminantGradient_eq_remainder_sum φ z z t,map_add]

@[simp] theorem classicalAntiDiscriminantGradientFourierCoefficients_apply {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (P : (ℂ × ℂ) →L[ℝ] ℂ) (k : ℤ) :
    classicalAntiDiscriminantGradientFourierCoefficients hq φ z w P k =
      intervalFourierCoefficient 1 (fun t => P (classicalAntiDiscriminantGradientRemainder φ z w t)) k := by
  have hc (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ) :
      Continuous (fun t => P (classicalEndpointGradientRemainder φ z w v L t)) :=
    P.continuous.comp (contDiff_classicalEndpointGradientRemainder φ z w v L).continuous
  change intervalFourierCoefficient 1 (fun t => P (classicalEndpointGradientRemainder φ z w (0,1) _ t)) k+
    intervalFourierCoefficient 1 (fun t => P (classicalEndpointGradientRemainder φ z w (1,0) _ t)) k = _
  rw [← intervalFourierCoefficient_add 1 _ _ (hc (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ))
    (hc (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ))]
  congr 1
  funext t
  rw [classicalAntiDiscriminantGradientRemainder_eq_sum,map_add]

/-- The anti-discriminant coefficients subtract the exact signed physical Fourier waves. -/
theorem classicalAntiDiscriminantGradientFourierCoefficients_lattice_apply {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℤ) (P : (ℂ × ℂ) →L[ℝ] ℂ) (k : ℤ) :
    classicalAntiDiscriminantGradientFourierCoefficients hq φ z ((Real.pi : ℂ)*(n : ℂ)) P k =
      intervalFourierCoefficient 1 (fun t => P (classicalAntiDiscriminantGradient φ z t-
        (I*cos ((Real.pi : ℂ)*(n : ℂ))*wave (2*n) t,
         -I*cos ((Real.pi : ℂ)*(n : ℂ))*wave (-(2*n)) t))) k := by
  rw [classicalAntiDiscriminantGradientFourierCoefficients_apply]
  apply intervalFourierCoefficient_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  dsimp only
  rw [classicalAntiDiscriminantGradientRemainder_lattice φ z n ⟨t,ht'⟩]

end NLS.ZakharovShabat
