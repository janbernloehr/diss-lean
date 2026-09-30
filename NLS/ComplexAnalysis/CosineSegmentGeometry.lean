import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.LinearCombination

/-!
# Cosine coordinates for complex gap segments

The entire map `τ + δ cos θ` sends the real axis to the closed gap
from `τ-δ` to `τ+δ`. Every nonreal angle avoids that segment when
the gap is noncollapsed. Its derivative cancels a square root of
the endpoint polynomial.
-/

noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

def cosineGapPoint (τ δ θ : ℂ) : ℂ := τ+δ*Complex.cos θ

theorem cosineGapPoint_real_mem_segment (τ δ : ℂ) (t : ℝ) :
    cosineGapPoint τ δ (t:ℂ) ∈ segment ℝ (τ-δ) (τ+δ) := by
  have ht : (Real.cos t+1)/2 ∈ Icc (0:ℝ) 1 := by
    constructor <;> linarith [Real.neg_one_le_cos t,Real.cos_le_one t]
  convert lineMap_mem_segment ℝ (τ-δ) (τ+δ) ht using 1
  simp only [cosineGapPoint,AffineMap.lineMap_apply_module,Complex.real_smul,
    Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_div,Complex.ofReal_add,
    Complex.ofReal_ofNat,Complex.ofReal_cos]
  ring

theorem cosineGapPoint_not_mem_segment (τ δ θ : ℂ) (hδ : δ ≠ 0) (hθ : θ.im ≠ 0) :
    cosineGapPoint τ δ θ ∉ segment ℝ (τ-δ) (τ+δ) := by
  intro hs
  obtain ⟨t,ht,heq⟩ := by rw [segment_eq_image_lineMap] at hs; exact hs
  have he : δ*Complex.cos θ = δ*((2*t-1:ℝ):ℂ) := by
    rw [AffineMap.lineMap_apply_module] at heq
    simp only [cosineGapPoint,Complex.real_smul,Complex.ofReal_sub,
      Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_one] at heq ⊢
    linear_combination -heq
  have hcos : Complex.cos θ = Complex.cos (Real.arccos (2*t-1):ℂ) := by
    rw [← Complex.ofReal_cos,Real.cos_arccos (by linarith [ht.1] : -1 ≤ 2*t-1)
      (by linarith [ht.2] : 2*t-1 ≤ 1)]
    exact mul_left_cancel₀ hδ he
  obtain ⟨k,hk|hk⟩ := Complex.cos_eq_cos_iff.mp hcos
  · have hi := congrArg Complex.im hk
    exact hθ (by simpa using hi.symm)
  · have hi := congrArg Complex.im hk
    exact hθ (by simpa using hi.symm)

theorem sin_ne_zero_of_im_ne_zero (θ : ℂ) (hθ : θ.im ≠ 0) : Complex.sin θ ≠ 0 := by
  intro hs
  obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hs
  apply hθ
  rw [hk]
  simp

theorem cosineGapPoint_endpoint_factor (τ δ θ : ℂ) :
    (τ-δ-cosineGapPoint τ δ θ)*(τ+δ-cosineGapPoint τ δ θ) =
      -(δ^2*Complex.sin θ^2) := by
  dsimp [cosineGapPoint]
  linear_combination δ^2 * Complex.sin_sq_add_cos_sq θ

theorem hasDerivAt_cosineGapPoint (τ δ θ : ℂ) :
    HasDerivAt (cosineGapPoint τ δ) (-δ*Complex.sin θ) θ := by
  convert ((Complex.hasDerivAt_cos θ).const_mul δ).const_add τ using 1 <;>
    first | rfl | ring

end NLS.ComplexAnalysis
