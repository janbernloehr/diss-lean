import NLS.ComplexAnalysis.QuadraticCauchyEquation
import NLS.ComplexAnalysis.CosineSegmentGeometry
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Regular cosine pullbacks of quadratic root primitives

Multiplication by the cosine root cancels the singularity at both gap
endpoints. The quadratic differential equation gives its derivative
without division by the sine. A real rotated numerator therefore gives
a real primitive on the whole real angle axis.
-/

noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

theorem im_eq_zero_of_cosineGapPoint_mem_segment (τ δ θ : ℂ) (hδ : δ ≠ 0)
    (hθ : cosineGapPoint τ δ θ ∈ segment ℝ (τ-δ) (τ+δ)) : θ.im = 0 := by
  by_contra h
  exact cosineGapPoint_not_mem_segment τ δ θ hδ h hθ

def quadraticCosinePrimitive (τ δ : ℂ) (H : ℂ → ℂ) (θ : ℂ) : ℂ :=
  (-I*δ*Complex.sin θ)*H (cosineGapPoint τ δ θ)

/-- The root equation cancels the cosine Jacobian, also at sine zeros. -/
theorem hasDerivAt_quadraticCosinePrimitive
    (τ δ θ g : ℂ) (H : ℂ → ℂ)
    (hH : DifferentiableAt ℂ H (cosineGapPoint τ δ θ))
    (heq : quadraticRootPolynomial τ (δ^2) (cosineGapPoint τ δ θ)*
        deriv H (cosineGapPoint τ δ θ)+
      (cosineGapPoint τ δ θ-τ)*H (cosineGapPoint τ δ θ) = g) :
    HasDerivAt (quadraticCosinePrimitive τ δ H) (-I*g) θ := by
  have hd := ((Complex.hasDerivAt_sin θ).const_mul (-I*δ)).fun_mul
    (hH.hasDerivAt.comp θ (hasDerivAt_cosineGapPoint τ δ θ))
  have hpoly : quadraticRootPolynomial τ (δ^2) (cosineGapPoint τ δ θ) =
      -(δ^2*Complex.sin θ^2) := by
    dsimp only [quadraticRootPolynomial,cosineGapPoint]
    linear_combination δ^2*(Complex.sin_sq_add_cos_sq θ)
  rw [hpoly] at heq
  convert! hd using 1 <;> try rfl
  dsimp only [cosineGapPoint,Function.comp_def] at heq ⊢
  linear_combination I*heq

/-- A real rotated right-hand side makes the cosine primitive real.
The zero value at pi fixes its imaginary integration constant. -/
theorem quadraticCosinePrimitive_im_eq_zero
    (τ δ : ℂ) (H g : ℂ → ℂ)
    (hH : ∀ t : ℝ, DifferentiableAt ℂ H (cosineGapPoint τ δ (t:ℂ)))
    (heq : ∀ t : ℝ, quadraticRootPolynomial τ (δ^2) (cosineGapPoint τ δ (t:ℂ))*
        deriv H (cosineGapPoint τ δ (t:ℂ))+
      (cosineGapPoint τ δ (t:ℂ)-τ)*H (cosineGapPoint τ δ (t:ℂ)) =
        g (cosineGapPoint τ δ (t:ℂ)))
    (hg : ∀ t : ℝ, (-I*g (cosineGapPoint τ δ (t:ℂ))).im = 0)
    (t : ℝ) : (quadraticCosinePrimitive τ δ H (t:ℂ)).im = 0 := by
  have hd (x : ℝ) : HasDerivAt
      (fun x : ℝ => (quadraticCosinePrimitive τ δ H (x:ℂ)).im) 0 x := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x
      ((hasDerivAt_quadraticCosinePrimitive τ δ (x:ℂ)
        (g (cosineGapPoint τ δ (x:ℂ))) H (hH x) (heq x)).comp_ofReal)
    change HasDerivAt _ (-I*g (cosineGapPoint τ δ (x:ℂ))).im x at h
    rwa [hg x] at h
  have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) t Real.pi
  simpa [quadraticCosinePrimitive] using hc

end NLS.ComplexAnalysis
