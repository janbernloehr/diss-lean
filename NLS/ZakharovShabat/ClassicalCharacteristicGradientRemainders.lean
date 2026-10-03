import NLS.ZakharovShabat.ClassicalEndpointGradientErrorIntegral
import NLS.ZakharovShabat.ClassicalFreePotentialGradients

/-! # Trace and anti-trace gradient errors

The discriminant gradient is a sum of two diagonal endpoint errors.
The anti-discriminant gradient minus its free reference is the analogous
off-diagonal sum. The lattice reference retains the signed physical waves.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

/-- The actual discriminant gradient is the sum of its diagonal endpoint gradients. -/
theorem classicalDiscriminantGradient_eq_endpoint_sum (φ : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    classicalDiscriminantGradient φ z t =
      classicalEndpointGradient φ z (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) t+
      classicalEndpointGradient φ z (0,1) (ContinuousLinearMap.snd ℂ ℂ ℂ) t := by
  simp only [classicalDiscriminantGradient,classicalEndpointGradient,classicalMonodromy,
    classicalFundamentalMatrix,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
  apply Prod.ext <;> dsimp <;> ring

/-- The lower diagonal free endpoint gradient also vanishes identically. -/
theorem classicalFreeEndpointGradient_snd_second (z : ℂ) (t : ℝ) :
    classicalFreeEndpointGradient z (0,1) (ContinuousLinearMap.snd ℂ ℂ ℂ) t = 0 := by
  simp [classicalFreeEndpointGradient,endpointGradientPolynomial,classicalFreeEndpointGradientData,
    classicalFreeVector]

/-- Either free reference can be used for the discriminant's two zero diagonal terms. -/
theorem classicalDiscriminantGradient_eq_remainder_sum (φ : Curve (ℂ × ℂ)) (z w : ℂ) (t : ℝ) :
    classicalDiscriminantGradient φ z t =
      classicalEndpointGradientRemainder φ z w (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) t+
      classicalEndpointGradientRemainder φ z w (0,1) (ContinuousLinearMap.snd ℂ ℂ ℂ) t := by
  simp only [classicalEndpointGradientRemainder,classicalFreeEndpointGradient_fst_first,
    classicalFreeEndpointGradient_snd_second,sub_zero,classicalDiscriminantGradient_eq_endpoint_sum]

/-- The free reference uses both off-diagonal entries. -/
def classicalFreeAntiDiscriminantGradient (w : ℂ) (t : ℝ) : ℂ × ℂ :=
  classicalFreeEndpointGradient w (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) t+
  classicalFreeEndpointGradient w (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) t

/-- The actual anti-discriminant gradient error at any free reference frequency. -/
def classicalAntiDiscriminantGradientRemainder (φ : Curve (ℂ × ℂ)) (z w : ℂ) (t : ℝ) : ℂ × ℂ :=
  classicalAntiDiscriminantGradient φ z t-classicalFreeAntiDiscriminantGradient w t

theorem classicalAntiDiscriminantGradientRemainder_eq_sum
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (t : ℝ) :
    classicalAntiDiscriminantGradientRemainder φ z w t =
      classicalEndpointGradientRemainder φ z w (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) t+
      classicalEndpointGradientRemainder φ z w (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) t := by
  simp only [classicalAntiDiscriminantGradientRemainder,classicalAntiDiscriminantGradient,
    classicalFreeAntiDiscriminantGradient,classicalEndpointGradientRemainder]
  abel

/-- The lattice reference equals the actual zero-potential gradient on the interval. -/
theorem classicalFreeAntiDiscriminantGradient_lattice (n : ℤ) (t : Icc (0 : ℝ) 1) :
    classicalFreeAntiDiscriminantGradient ((Real.pi : ℂ)*(n : ℂ)) t =
      (I*cos ((Real.pi : ℂ)*(n : ℂ))*wave (2*n) t,
       -I*cos ((Real.pi : ℂ)*(n : ℂ))*wave (-(2*n)) t) := by
  rw [classicalFreeAntiDiscriminantGradient,← classicalEndpointGradient_free _ _ _ t,
    ← classicalEndpointGradient_free _ _ _ t]
  exact classicalAntiDiscriminantGradient_free_lattice n t t.property

/-- Exact physical-wave subtraction in G.6, in the unmultiplied derivative convention. -/
theorem classicalAntiDiscriminantGradientRemainder_lattice
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℤ) (t : Icc (0 : ℝ) 1) :
    classicalAntiDiscriminantGradientRemainder φ z ((Real.pi : ℂ)*(n : ℂ)) t =
      classicalAntiDiscriminantGradient φ z t-
        (I*cos ((Real.pi : ℂ)*(n : ℂ))*wave (2*n) t,
         -I*cos ((Real.pi : ℂ)*(n : ℂ))*wave (-(2*n)) t) := by
  rw [classicalAntiDiscriminantGradientRemainder,classicalFreeAntiDiscriminantGradient_lattice]

/-- Multiplication by i gives the exact signed free-wave convention used in G.6. -/
theorem classicalAntiDiscriminantGradientRemainder_lattice_mul_I
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (n : ℤ) (t : Icc (0 : ℝ) 1) :
    I • classicalAntiDiscriminantGradientRemainder φ z ((Real.pi : ℂ)*(n : ℂ)) t =
      I • classicalAntiDiscriminantGradient φ z t-
        (-1 : ℂ)^n • (-wave (2*n) t,wave (-(2*n)) t) := by
  rw [classicalAntiDiscriminantGradientRemainder_lattice,
    show cos ((Real.pi : ℂ)*(n : ℂ)) = (-1 : ℂ)^n by
      rw [show (Real.pi : ℂ)*(n : ℂ) = (((n : ℝ)*Real.pi : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cos,Real.cos_int_mul_pi]
      push_cast
      rfl]
  apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,Prod.fst_sub,Prod.snd_sub,smul_eq_mul]
  all_goals ring_nf; simp only [I_sq]; ring

end NLS.ZakharovShabat
