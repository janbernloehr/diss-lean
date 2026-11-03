import NLS.ComplexAnalysis.QuadraticCosinePrimitive

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



def regularQuadraticCosinePrimitive (τ δ : ℂ) (H : ℂ → ℂ) (θ : ℂ) : ℂ :=
  δ*Complex.sin θ*H (cosineGapPoint τ δ θ)

theorem hasDerivAt_regularQuadraticCosinePrimitive
    (τ δ θ g : ℂ) (H : ℂ → ℂ)
    (hH : DifferentiableAt ℂ H (cosineGapPoint τ δ θ))
    (heq : quadraticRootPolynomial τ (δ^2) (cosineGapPoint τ δ θ)*deriv H (cosineGapPoint τ δ θ)+
      (cosineGapPoint τ δ θ-τ)*H (cosineGapPoint τ δ θ) = g) :
    HasDerivAt (regularQuadraticCosinePrimitive τ δ H) g θ := by
  have hd := (hasDerivAt_quadraticCosinePrimitive τ δ θ g H hH heq).const_mul I
  have he : regularQuadraticCosinePrimitive τ δ H = fun e => I*quadraticCosinePrimitive τ δ H e := by
    funext e
    simp only [regularQuadraticCosinePrimitive,quadraticCosinePrimitive]
    ring_nf
    simp only [I_sq]
    ring
  rw [he]
  simpa only [← mul_assoc,mul_neg,I_mul_I,neg_neg,one_mul] using hd

theorem regularQuadraticCosinePrimitive_pi (τ δ : ℂ) (H : ℂ → ℂ) :
    regularQuadraticCosinePrimitive τ δ H (Real.pi : ℂ) = 0 := by
  simp only [regularQuadraticCosinePrimitive,Complex.sin_pi,mul_zero,zero_mul]

end NLS.ComplexAnalysis
