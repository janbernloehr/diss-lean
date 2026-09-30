import NLS.ComplexAnalysis.CosineSegmentGeometry
import Mathlib.Topology.Algebra.Field

/-!
# The constant differential factor on each cosine sheet

Dividing the derivative of a cosine gap coordinate by a square root
of its endpoint polynomial gives a coefficient whose square is `-1`.
It is constant on every connected nonreal angle chart. Opposite pure
imaginary angles map to the same spectral point and give opposite
coefficients, independently of which square-root sign is used.
-/

noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

def cosineRootCoefficient (Q : ℂ → ℂ) (τ δ θ : ℂ) : ℂ :=
  (-δ*Complex.sin θ) / Q (cosineGapPoint τ δ θ)

theorem cosineRootCoefficient_neg (Q : ℂ → ℂ) (τ δ θ : ℂ) :
    cosineRootCoefficient Q τ δ (-θ) = -cosineRootCoefficient Q τ δ θ := by
  simp only [cosineRootCoefficient,cosineGapPoint,Complex.cos_neg,Complex.sin_neg,
    mul_neg,neg_div]

theorem cosineRootCoefficient_sq (Q : ℂ → ℂ) (τ δ θ : ℂ)
    (hδ : δ ≠ 0) (hθ : θ.im ≠ 0)
    (hsq : Q (cosineGapPoint τ δ θ)^2 =
      (τ-δ-cosineGapPoint τ δ θ)*(τ+δ-cosineGapPoint τ δ θ)) :
    cosineRootCoefficient Q τ δ θ ^ 2 = -1 := by
  have hs := sin_ne_zero_of_im_ne_zero θ hθ
  rw [cosineGapPoint_endpoint_factor] at hsq
  have hQ : Q (cosineGapPoint τ δ θ) ≠ 0 := by
    intro h
    have hn : -(δ^2*Complex.sin θ^2) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hδ) (pow_ne_zero 2 hs))
    apply hn
    rw [← hsq,h]
    norm_num
  unfold cosineRootCoefficient
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 hQ)).2
  rw [hsq]
  ring

/-- The differential coefficient is fixed on each connected nonreal
angle chart. Only continuity of the chosen square root is required. -/
theorem cosineRootCoefficient_eq_on_connected
    (Q : ℂ → ℂ) (τ δ : ℂ) (S : Set ℂ) (hδ : δ ≠ 0)
    (hS : IsPreconnected S) (hθ : ∀ θ ∈ S, θ.im ≠ 0)
    (hQ : ContinuousOn (fun θ => Q (cosineGapPoint τ δ θ)) S)
    (hsq : ∀ θ ∈ S, Q (cosineGapPoint τ δ θ)^2 =
      (τ-δ-cosineGapPoint τ δ θ)*(τ+δ-cosineGapPoint τ δ θ))
    (a : ℂ) (ha : a ∈ S) :
    ∀ θ ∈ S, cosineRootCoefficient Q τ δ θ = cosineRootCoefficient Q τ δ a := by
  have hQne (θ : ℂ) (hθS : θ ∈ S) : Q (cosineGapPoint τ δ θ) ≠ 0 := by
    intro h
    have hs := hsq θ hθS
    rw [cosineGapPoint_endpoint_factor,h,zero_pow (by norm_num : 2 ≠ 0)] at hs
    exact (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 2 hδ)
      (pow_ne_zero 2 (sin_ne_zero_of_im_ne_zero θ (hθ θ hθS))))) hs.symm
  have hcont : ContinuousOn (cosineRootCoefficient Q τ δ) S :=
    (by fun_prop : ContinuousOn (fun θ : ℂ => -δ*Complex.sin θ) S).div hQ hQne
  have hasq := cosineRootCoefficient_sq Q τ δ a hδ (hθ a ha) (hsq a ha)
  have hane : cosineRootCoefficient Q τ δ a ≠ 0 := by
    intro h
    rw [h] at hasq
    norm_num at hasq
  exact hS.eq_of_sq_eq hcont continuousOn_const
    (fun θ hθS => (cosineRootCoefficient_sq Q τ δ θ hδ (hθ θ hθS) (hsq θ hθS)).trans hasq.symm)
    (fun _ => hane) ha rfl

end NLS.ComplexAnalysis
