import NLS.ComplexAnalysis.AffineLoopHomotopy
import NLS.ComplexAnalysis.PiecewiseSquareContour

/-! # Squared positive-frequency circles and real-band energy circles

The affine deformation preserves the sign of the imaginary part. At its
real crossings both endpoints lie in the same open real band. No common
convex isolating disc for the two energy contours is needed.
-/
noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

private theorem real_circle_re (c r θ : ℝ) :
    (circleMap (c : ℂ) r θ).re = c+r*Real.cos θ := by
  have h := congrArg Complex.re (circleMap_sub_center (c : ℂ) r θ)
  have he : (circleMap (c : ℂ) r θ).re-c = r*Real.cos θ := by
    simpa only [sub_re,ofReal_re,circleMap_zero_re] using h
  linarith

private theorem real_circle_im (c r θ : ℝ) :
    (circleMap (c : ℂ) r θ).im = r*Real.sin θ := by
  have h := congrArg Complex.im (circleMap_sub_center (c : ℂ) r θ)
  simpa only [sub_im,ofReal_im,sub_zero,circleMap_zero_im] using h

theorem lineMap_squared_circle_mem_real_bands
    (c r d R l a b u : ℝ) (hr : 0 < r) (hrc : r < c) (hR : 0 < R)
    (hleft₀ : (c-r)^2 ∈ Ioo l a) (hleft₁ : d-R ∈ Ioo l a)
    (hright₀ : (c+r)^2 ∈ Ioo b u) (hright₁ : d+R ∈ Ioo b u)
    (s : I) (θ : ℝ) :
    let z := AffineMap.lineMap ((circleMap (c : ℂ) r θ)^2)
      (circleMap (d : ℂ) R θ) (s : ℝ)
    z.im ≠ 0 ∨ z.re ∈ Ioo l a ∨ z.re ∈ Ioo b u := by
  let z := circleMap (c : ℂ) r θ
  let w := circleMap (d : ℂ) R θ
  let v := AffineMap.lineMap (z^2) w (s:ℝ)
  have hre : v.re = (1-(s:ℝ))*(z.re^2-z.im^2)+(s:ℝ)*w.re := by
    change (AffineMap.lineMap (z^2) w (s:ℝ)).re = _
    simp only [AffineMap.lineMap_apply_module,Complex.real_smul,add_re,mul_re,ofReal_re,ofReal_im,
      zero_mul,sub_zero,pow_two]
  have him : v.im = Real.sin θ*((1-(s:ℝ))*2*r*z.re+(s:ℝ)*R) := by
    change (AffineMap.lineMap (z^2) w (s:ℝ)).im = _
    simp only [AffineMap.lineMap_apply_module,Complex.real_smul,add_im,mul_im,ofReal_re,ofReal_im,
      zero_mul,add_zero,pow_two]
    rw [show z.im = r*Real.sin θ from real_circle_im c r θ,
      show w.im = R*Real.sin θ from real_circle_im d R θ]
    ring
  have hz : 0 < z.re := by
    rw [show z.re = c+r*Real.cos θ from real_circle_re c r θ]
    nlinarith [Real.neg_one_le_cos θ]
  have hcoef : 0 < (1-(s:ℝ))*2*r*z.re+(s:ℝ)*R := by
    have hA : 0 < (2:ℝ)*r*z.re := mul_pos (mul_pos (by norm_num) hr) hz
    have h := (convex_Ioi (0:ℝ)).lineMap_mem hA hR s.property
    simpa only [AffineMap.lineMap_apply_module,smul_eq_mul,mul_assoc,mem_Ioi] using h
  by_cases hs : Real.sin θ = 0
  · have hc : Real.cos θ = 1 ∨ Real.cos θ = -1 := by
      have hc2 : Real.cos θ ^ 2 = 1^2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hc2
    rcases hc with hc | hc
    · apply Or.inr ∘ Or.inr
      rw [hre,show z.re = c+r*Real.cos θ from real_circle_re c r θ,
        show z.im = r*Real.sin θ from real_circle_im c r θ,
        show w.re = d+R*Real.cos θ from real_circle_re d R θ,hc,hs]
      simpa only [mul_one,mul_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,
        AffineMap.lineMap_apply_module,smul_eq_mul] using
          (convex_Ioo b u).lineMap_mem hright₀ hright₁ s.property
    · apply Or.inr ∘ Or.inl
      rw [hre,show z.re = c+r*Real.cos θ from real_circle_re c r θ,
        show z.im = r*Real.sin θ from real_circle_im c r θ,
        show w.re = d+R*Real.cos θ from real_circle_re d R θ,hc,hs]
      simpa only [mul_neg_one,mul_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,← sub_eq_add_neg,
        AffineMap.lineMap_apply_module,smul_eq_mul] using
          (convex_Ioo l a).lineMap_mem hleft₀ hleft₁ s.property
  · exact Or.inl (by rw [him];exact mul_ne_zero hs hcoef.ne')

theorem affine_squared_circle_mem_real_bands
    (c r d R l a b u : ℝ) (hr : 0 < r) (hrc : r < c) (hR : 0 < R)
    (hleft₀ : (c-r)^2 ∈ Ioo l a) (hleft₁ : d-R ∈ Ioo l a)
    (hright₀ : (c+r)^2 ∈ Ioo b u) (hright₁ : d+R ∈ Ioo b u)
    (s t : I) :
    let H := ContinuousMap.Homotopy.affine
      (squarePath (circlePath (c : ℂ) r) : C(I,ℂ))
      (circlePath (d : ℂ) R : C(I,ℂ))
    (H (s,t)).im ≠ 0 ∨ (H (s,t)).re ∈ Ioo l a ∨ (H (s,t)).re ∈ Ioo b u := by
  dsimp only
  rw [ContinuousMap.Homotopy.affine_apply]
  exact lineMap_squared_circle_mem_real_bands c r d R l a b u hr hrc hR
    hleft₀ hleft₁ hright₀ hright₁ s ((2*Real.pi)*(t:ℝ))

theorem circleIntegral_square_eq_of_real_bands
    (f : ℂ → ℂ) (D : Set ℂ) (c r d R l a b u : ℝ)
    (hr : 0 < r) (hrc : r < c) (hR : 0 < R)
    (hleft₀ : (c-r)^2 ∈ Ioo l a) (hleft₁ : d-R ∈ Ioo l a)
    (hright₀ : (c+r)^2 ∈ Ioo b u) (hright₁ : d+R ∈ Ioo b u)
    (hD : ∀ z : ℂ,z.im ≠ 0 ∨ z.re ∈ Ioo l a ∨ z.re ∈ Ioo b u → z ∈ D)
    (hf : AnalyticOnNhd ℂ f D) :
    (∮ z in C((c:ℂ),r),2*z*f (z^2)) = ∮ E in C((d:ℂ),R),f E := by
  let H := ContinuousMap.Homotopy.affine
    (squarePath (circlePath (c : ℂ) r) : C(I,ℂ))
    (circlePath (d : ℂ) R : C(I,ℂ))
  have hmem (s t : I) : H (s,t) ∈ D := hD _
    (affine_squared_circle_mem_real_bands c r d R l a b u hr hrc hR hleft₀ hleft₁ hright₀ hright₁ s t)
  have hclosed : IsClosed (range H) := isCompact_range H.continuous |>.isClosed
  have hsmooth : ContDiffOn ℝ 2 (squarePath (circlePath (c : ℂ) r)).extend (Icc 0 1) :=
    (circlePath_contDiffOn (c : ℂ) r).pow 2
  have heq := curveIntegral_eq_of_holomorphic_homotopy f H affineHomotopy_loop
    (t := range H) (fun s _ t _ => mem_range_self (s,t))
    (by
      rw [hclosed.closure_eq]
      rintro z ⟨⟨s,t⟩,rfl⟩
      exact (hf _ (hmem s t)).differentiableAt)
    (affineHomotopy_contDiffOn hsmooth (circlePath_contDiffOn (d : ℂ) R))
  simpa only [curveIntegral_squarePath _ ((circlePath_contDiffOn (c : ℂ) r).of_le (by norm_num)),
    curveIntegral_circlePath] using heq

end NLS.ComplexAnalysis
