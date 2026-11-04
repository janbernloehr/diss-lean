import NLS.ComplexAnalysis.ShiftedSquaredCircle
import NLS.ComplexAnalysis.AffineLoopHomotopy

/-! # Homotopy of two shifted squared circles through matched real bands

Positive frequency half-planes give a common imaginary sign. At real
crossings, convexity of the matched bands keeps the entire homotopy
in the analytic domain. The conclusion concerns actual loop integrals.
-/
noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- Real and imaginary coordinates of a real-centered frequency circle. -/
private theorem shiftedCircle_coordinates (c r theta : ℝ) :
    (circleMap (c : ℂ) r theta).re = c+r*Real.cos theta ∧
      (circleMap (c : ℂ) r theta).im = r*Real.sin theta := by
  have h := circleMap_sub_center (c : ℂ) r theta
  constructor
  · have he := congrArg Complex.re h
    simp only [sub_re,ofReal_re,circleMap_zero_re] at he
    linarith
  · have he := congrArg Complex.im h
    simpa only [sub_im,ofReal_im,sub_zero,circleMap_zero_im] using he

/-- The affine homotopy of two shifted squared positive-frequency circles stays nonreal or in the two matched real bands. -/
theorem shiftedSquaredCircle_affine_mem_real_bands
    (c r d R a b l₀ u₀ l₁ u₁ : ℝ)
    (hr : 0 < r) (hrc : r < c) (hR : 0 < R) (hRd : R < d)
    (hlc : (c-r)^2-a ∈ Ioo l₀ u₀) (hld : (d-R)^2-b ∈ Ioo l₀ u₀)
    (hrc' : (c+r)^2-a ∈ Ioo l₁ u₁) (hrd : (d+R)^2-b ∈ Ioo l₁ u₁)
    (s : I) (theta : ℝ) :
    let v := AffineMap.lineMap ((circleMap (c : ℂ) r theta)^2-(a : ℂ))
      ((circleMap (d : ℂ) R theta)^2-(b : ℂ)) (s : ℝ)
    v.im ≠ 0 ∨ v.re ∈ Ioo l₀ u₀ ∨ v.re ∈ Ioo l₁ u₁ := by
  let z := circleMap (c : ℂ) r theta
  let w := circleMap (d : ℂ) R theta
  let v := AffineMap.lineMap (z^2-(a : ℂ)) (w^2-(b : ℂ)) (s : ℝ)
  have hz := shiftedCircle_coordinates c r theta
  have hw := shiftedCircle_coordinates d R theta
  have hre : v.re = (1-(s : ℝ))*(z.re^2-z.im^2-a)+(s : ℝ)*(w.re^2-w.im^2-b) := by
    simp only [v,AffineMap.lineMap_apply_module,Complex.real_smul,add_re,sub_re,pow_two,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
  have him : v.im = Real.sin theta*((1-(s : ℝ))*2*r*z.re+(s : ℝ)*2*R*w.re) := by
    simp only [v,AffineMap.lineMap_apply_module,Complex.real_smul,add_im,sub_im,pow_two,mul_im,ofReal_im,ofReal_re,sub_zero]
    rw [show z.im = r*Real.sin theta from hz.2,show w.im = R*Real.sin theta from hw.2]
    ring
  have hzpos : 0 < z.re := by
    rw [show z.re = c+r*Real.cos theta from hz.1]
    nlinarith [Real.neg_one_le_cos theta]
  have hwpos : 0 < w.re := by
    rw [show w.re = d+R*Real.cos theta from hw.1]
    nlinarith [Real.neg_one_le_cos theta]
  have hcoef : 0 < (1-(s : ℝ))*2*r*z.re+(s : ℝ)*2*R*w.re := by
    have hp := (convex_Ioi (0 : ℝ)).lineMap_mem
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hr) hzpos)
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hR) hwpos) s.property
    simpa only [AffineMap.lineMap_apply_module,smul_eq_mul,mem_Ioi,mul_assoc] using hp
  by_cases hs : Real.sin theta = 0
  · have hc : Real.cos theta = 1 ∨ Real.cos theta = -1 := by
      have he : Real.cos theta ^ 2 = 1^2 := by nlinarith [Real.sin_sq_add_cos_sq theta]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp he
    rcases hc with hc | hc
    · apply Or.inr ∘ Or.inr
      rw [hre,show z.re = c+r*Real.cos theta from hz.1,show z.im = r*Real.sin theta from hz.2,
        show w.re = d+R*Real.cos theta from hw.1,show w.im = R*Real.sin theta from hw.2,hc,hs]
      simpa only [mul_one,mul_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,
        AffineMap.lineMap_apply_module,smul_eq_mul] using (convex_Ioo l₁ u₁).lineMap_mem hrc' hrd s.property
    · apply Or.inr ∘ Or.inl
      rw [hre,show z.re = c+r*Real.cos theta from hz.1,show z.im = r*Real.sin theta from hz.2,
        show w.re = d+R*Real.cos theta from hw.1,show w.im = R*Real.sin theta from hw.2,hc,hs]
      simpa only [mul_neg_one,mul_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,← sub_eq_add_neg,
        AffineMap.lineMap_apply_module,smul_eq_mul] using (convex_Ioo l₀ u₀).lineMap_mem hlc hld s.property
  · exact Or.inl (by rw [him];exact mul_ne_zero hs hcoef.ne')

/-- Matched real crossing bands identify the actual integrals of analytic functions on two shifted squared circles. -/
theorem shiftedSquaredCircle_integral_eq_of_real_bands
    (f : ℂ → ℂ) (D : Set ℂ) (c r d R a b l₀ u₀ l₁ u₁ : ℝ)
    (hr : 0 < r) (hrc : r < c) (hR : 0 < R) (hRd : R < d)
    (hlc : (c-r)^2-a ∈ Ioo l₀ u₀) (hld : (d-R)^2-b ∈ Ioo l₀ u₀)
    (hrc' : (c+r)^2-a ∈ Ioo l₁ u₁) (hrd : (d+R)^2-b ∈ Ioo l₁ u₁)
    (hD : ∀ z : ℂ, z.im ≠ 0 ∨ z.re ∈ Ioo l₀ u₀ ∨ z.re ∈ Ioo l₁ u₁ → z ∈ D)
    (hf : AnalyticOnNhd ℂ f D) :
    (shiftedSquaredCircle (c : ℂ) r (a : ℂ)).integral f =
      (shiftedSquaredCircle (d : ℂ) R (b : ℂ)).integral f := by
  let H := ContinuousMap.Homotopy.affine
    (shiftedSquaredCirclePath (c : ℂ) r (a : ℂ) : C(I,ℂ))
    (shiftedSquaredCirclePath (d : ℂ) R (b : ℂ) : C(I,ℂ))
  have hmem (s t : I) : H (s,t) ∈ D := by
    apply hD
    rw [ContinuousMap.Homotopy.affine_apply]
    exact shiftedSquaredCircle_affine_mem_real_bands c r d R a b l₀ u₀ l₁ u₁ hr hrc hR hRd
      hlc hld hrc' hrd s ((2*Real.pi)*(t : ℝ))
  have hclosed : IsClosed (range H) := (isCompact_range H.continuous).isClosed
  have heq := curveIntegral_eq_of_holomorphic_homotopy f H affineHomotopy_loop
    (t := range H) (fun s _ t _ => mem_range_self (s,t))
    (by
      rw [hclosed.closure_eq]
      rintro z ⟨⟨s,t⟩,rfl⟩
      exact (hf _ (hmem s t)).differentiableAt)
    (affineHomotopy_contDiffOn (shiftedSquaredCirclePath_contDiffOn (c : ℂ) r (a : ℂ))
      (shiftedSquaredCirclePath_contDiffOn (d : ℂ) R (b : ℂ)))
  simpa only [shiftedSquaredCircle,PiecewiseC1Loop.integral_ofPath] using heq

end NLS.ComplexAnalysis
