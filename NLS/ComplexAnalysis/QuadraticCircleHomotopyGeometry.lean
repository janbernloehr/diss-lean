import NLS.ComplexAnalysis.AffineLoopHomotopy
import NLS.ComplexAnalysis.QuadraticEnergyLoop

noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- The quadratic image of a circle in the right half-plane and a real
energy circle meet the real axis on corresponding sides of the cut.
Their whole affine homotopy stays in the two bands or off the real axis. -/
theorem affine_quadratic_circle_mem_bands
    (b R c d r a₀ a₁ b₀ b₁ θ s : ℝ)
    (hR : 0<R) (hb : R<b) (hr : 0<r) (hs : s∈Icc (0:ℝ) 1)
    (hleft : (b-R)^2-c∈Ioo a₀ a₁) (hright : (b+R)^2-c∈Ioo b₀ b₁)
    (hrefleft : d-r∈Ioo a₀ a₁) (hrefright : d+r∈Ioo b₀ b₁) :
    let z := AffineMap.lineMap ((circleMap (b:ℂ) R θ)^2-(c:ℂ))
      (circleMap (d:ℂ) r θ) s
    z.im≠0 ∨ z.re∈Ioo a₀ a₁ ∨ z.re∈Ioo b₀ b₁ := by
  dsimp only
  let z := AffineMap.lineMap ((circleMap (b:ℂ) R θ)^2-(c:ℂ))
    (circleMap (d:ℂ) r θ) s
  have hbr : 0<b+R*Real.cos θ := by nlinarith [Real.neg_one_le_cos θ]
  have hA : 0<2*R*(b+R*Real.cos θ) := by positivity
  have hfactor : 0<(1-s)*(2*R*(b+R*Real.cos θ))+s*r := by
    by_cases hs1 : s=1
    · simp only [hs1,sub_self,zero_mul,one_mul,zero_add]; exact hr
    · have hp : 0<1-s := sub_pos.mpr (lt_of_le_of_ne hs.2 hs1)
      exact add_pos_of_pos_of_nonneg (mul_pos hp hA) (mul_nonneg hs.1 hr.le)
  have him : z.im=Real.sin θ*((1-s)*(2*R*(b+R*Real.cos θ))+s*r) := by
    dsimp [z]
    simp [AffineMap.lineMap_apply,circleMap,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin,pow_two]
    ring
  by_cases hzi : z.im=0
  · have hsin : Real.sin θ=0 := by
      rw [hzi] at him
      exact (mul_eq_zero.mp him.symm).resolve_right hfactor.ne'
    have hcos2 : (Real.cos θ)^2=1^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    rcases eq_or_eq_neg_of_sq_eq_sq (Real.cos θ) 1 hcos2 with hcos | hcos
    · have hcirc (x t : ℝ) : circleMap (x:ℂ) t θ=((x+t:ℝ):ℂ) := by
        apply Complex.ext <;> simp [circleMap,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin,hsin,hcos]
      have he : z.re=AffineMap.lineMap ((b+R)^2-c) (d+r) s := by
        dsimp only [z]
        rw [hcirc b R,hcirc d r]
        rw [←ofReal_pow,←ofReal_sub]
        simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,sub_re,add_re,smul_re,
          ofReal_re]
      exact Or.inr (Or.inr (he ▸ (convex_Ioo b₀ b₁).lineMap_mem hright hrefright hs))
    · have hcirc (x t : ℝ) : circleMap (x:ℂ) t θ=((x-t:ℝ):ℂ) := by
        apply Complex.ext <;> simp [circleMap,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin,hsin,hcos,sub_eq_add_neg]
      have he : z.re=AffineMap.lineMap ((b-R)^2-c) (d-r) s := by
        dsimp only [z]
        rw [hcirc b R,hcirc d r]
        rw [←ofReal_pow,←ofReal_sub]
        simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,sub_re,add_re,smul_re,
          ofReal_re]
      exact Or.inr (Or.inl (he ▸ (convex_Ioo a₀ a₁).lineMap_mem hleft hrefleft hs))
  · exact Or.inl hzi

end NLS.ComplexAnalysis
