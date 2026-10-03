import NLS.ZakharovShabat.ClassicalEndpointGradientRemainder
import NLS.ZakharovShabat.ClassicalEndpointPoisson

/-! # The time equation for actual endpoint potential gradients

Subtracting the free equation leaves the spectral factor multiplying
only the already small gradient error. The remaining potential term
is a product of the actual solution and its endpoint dual solution.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The mixed product in the time equation of the endpoint gradient. -/
def classicalEndpointGradientMixed (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (s : ℝ) : ℂ :=
  let a := classicalSolution φ z (1,0) s
  let b := classicalSolution φ z (0,1) s
  let u := classicalSolution φ z v s
  let α := L (classicalSolution φ z (1,0) 1)
  let β := L (classicalSolution φ z (0,1) 1)
  (α*b.1-β*a.1)*u.2+(α*b.2-β*a.2)*u.1

/-- The exact time equation retains the original potential-component signs. -/
theorem hasDerivAt_classicalEndpointGradient
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalEndpointGradient φ z v L)
      (2*I*z*(classicalEndpointGradient φ z v L t).1+(φ t).2*classicalEndpointGradientMixed φ z v L t,
       -2*I*z*(classicalEndpointGradient φ z v L t).2-(φ t).1*classicalEndpointGradientMixed φ z v L t) t := by
  have ha := hasDerivAt_classicalSolution φ z (1,0) t
  have hb := hasDerivAt_classicalSolution φ z (0,1) t
  have hu := hasDerivAt_classicalSolution φ z v t
  let α := L (classicalSolution φ z (1,0) 1)
  let β := L (classicalSolution φ z (0,1) 1)
  have h1 := (((HasFDerivAt.hasDerivAt hb.snd).const_mul α).sub
    ((HasFDerivAt.hasDerivAt ha.snd).const_mul β)).const_mul I |>.mul (HasFDerivAt.hasDerivAt hu.snd)
  have h2 := (((HasFDerivAt.hasDerivAt hb.fst).const_mul α).sub
    ((HasFDerivAt.hasDerivAt ha.fst).const_mul β)).const_mul I |>.mul (HasFDerivAt.hasDerivAt hu.fst)
  convert! h1.prodMk h2 using 1
  apply Prod.ext
  all_goals simp only [classicalEndpointGradient,classicalEndpointGradientMixed,classicalODECoefficient_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul,α,β]
  all_goals dsimp; ring_nf; simp only [I_sq]; ring

/-- The mixed term is the product of the actual solution and its dual solution. -/
theorem classicalEndpointGradientMixed_eq_dual_product
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (t : Icc (0 : ℝ) 1) :
    classicalEndpointGradientMixed φ z v L t =
      (classicalSolution φ z (classicalEndpointDualInitial φ z L) t).1*(classicalSolution φ z v t).2+
      (classicalSolution φ z (classicalEndpointDualInitial φ z L) t).2*(classicalSolution φ z v t).1 := by
  rw [classicalEndpointDualSolution_eq_columns]
  rfl

/-- Differentiating the free gradient only multiplies its components by the free frequency. -/
theorem hasDerivAt_classicalFreeEndpointGradient (z : ℂ) (v : ℂ × ℂ)
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (t : ℝ) :
    HasDerivAt (classicalFreeEndpointGradient z v L)
      (2*I*z*(classicalFreeEndpointGradient z v L t).1,
       -2*I*z*(classicalFreeEndpointGradient z v L t).2) t := by
  have ha := hasDerivAt_classicalFreeVector z (1,0) t
  have hb := hasDerivAt_classicalFreeVector z (0,1) t
  have hu := hasDerivAt_classicalFreeVector z v t
  let α := L (classicalFreeVector z (1,0) 1)
  let β := L (classicalFreeVector z (0,1) 1)
  have h1 := (((HasFDerivAt.hasDerivAt hb.snd).const_mul α).sub
    ((HasFDerivAt.hasDerivAt ha.snd).const_mul β)).const_mul I |>.mul (HasFDerivAt.hasDerivAt hu.snd)
  have h2 := (((HasFDerivAt.hasDerivAt hb.fst).const_mul α).sub
    ((HasFDerivAt.hasDerivAt ha.fst).const_mul β)).const_mul I |>.mul (HasFDerivAt.hasDerivAt hu.fst)
  convert! h1.prodMk h2 using 1
  apply Prod.ext
  all_goals dsimp [classicalFreeEndpointGradient,endpointGradientPolynomial,classicalFreeEndpointGradientData,α,β]
  all_goals ring

/-- The gradient error satisfies an equation with a small spectral error and a potential term. -/
theorem hasDerivAt_classicalEndpointGradientRemainder
    (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalEndpointGradientRemainder φ z w v L)
      (2*I*z*(classicalEndpointGradientRemainder φ z w v L t).1+
        2*I*(z-w)*(classicalFreeEndpointGradient w v L t).1+(φ t).2*classicalEndpointGradientMixed φ z v L t,
       -2*I*z*(classicalEndpointGradientRemainder φ z w v L t).2-
        2*I*(z-w)*(classicalFreeEndpointGradient w v L t).2-(φ t).1*classicalEndpointGradientMixed φ z v L t) t := by
  apply ((hasDerivAt_classicalEndpointGradient φ z v L t).sub
    (hasDerivAt_classicalFreeEndpointGradient w v L t)).congr_deriv
  apply Prod.ext <;> dsimp [classicalEndpointGradientRemainder] <;> ring

end NLS.ZakharovShabat
