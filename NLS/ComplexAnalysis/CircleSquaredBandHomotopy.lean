import NLS.ComplexAnalysis.ShiftedSquaredCircleBandHomotopy
import NLS.ComplexAnalysis.SquaredCircleHomotopy
/-! # Frequency squares and energy circles through the same real bands

An actual smooth affine homotopy preserves the integral and its exact
quadratic Jacobian. Only r<c is needed, including the first frequency.
-/
noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

theorem circle_squaredCircle_affine_mem_real_bands
    (d R c r l₀ u₀ l₁ u₁ : ℝ) (hR : 0 < R) (hr : 0 < r) (hrc : r < c)
    (hld : d-R ∈ Ioo l₀ u₀) (hlc : (c-r)^2 ∈ Ioo l₀ u₀)
    (hud : d+R ∈ Ioo l₁ u₁) (huc : (c+r)^2 ∈ Ioo l₁ u₁)
    (s : I) (theta : ℝ) :
    let v := AffineMap.lineMap (circleMap (d : ℂ) R theta)
      ((circleMap (c : ℂ) r theta)^2) (s : ℝ)
    v.im ≠ 0 ∨ v.re ∈ Ioo l₀ u₀ ∨ v.re ∈ Ioo l₁ u₁ := by
  let z := circleMap (c : ℂ) r theta
  let w := circleMap (d : ℂ) R theta
  let v := AffineMap.lineMap w (z^2) (s : ℝ)
  have hzr : z.re = c+r*Real.cos theta := by
    have he := congrArg Complex.re (circleMap_sub_center (c : ℂ) r theta)
    simp only [sub_re,ofReal_re,circleMap_zero_re] at he
    linarith
  have hzi : z.im = r*Real.sin theta := by
    simpa only [sub_im,ofReal_im,sub_zero,circleMap_zero_im] using
      congrArg Complex.im (circleMap_sub_center (c : ℂ) r theta)
  have hwr : w.re = d+R*Real.cos theta := by
    have he := congrArg Complex.re (circleMap_sub_center (d : ℂ) R theta)
    simp only [sub_re,ofReal_re,circleMap_zero_re] at he
    linarith
  have hwi : w.im = R*Real.sin theta := by
    simpa only [sub_im,ofReal_im,sub_zero,circleMap_zero_im] using
      congrArg Complex.im (circleMap_sub_center (d : ℂ) R theta)
  have him : v.im = Real.sin theta*((1-(s : ℝ))*R+(s : ℝ)*2*r*z.re) := by
    simp only [v,AffineMap.lineMap_apply_module,Complex.real_smul,add_im,pow_two,mul_im,hwi,hzi,ofReal_re,ofReal_im,zero_mul,add_zero]
    ring
  have hre : v.re = (1-(s : ℝ))*w.re+(s : ℝ)*(z.re^2-z.im^2) := by
    simp only [v,AffineMap.lineMap_apply_module,Complex.real_smul,add_re,pow_two,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
  have hzpos : 0 < z.re := by rw [hzr];nlinarith [Real.neg_one_le_cos theta]
  have hcoef : 0 < (1-(s : ℝ))*R+(s : ℝ)*2*r*z.re := by
    have hp := (convex_Ioi (0 : ℝ)).lineMap_mem hR
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hr) hzpos) s.property
    simpa only [AffineMap.lineMap_apply_module,smul_eq_mul,mem_Ioi,mul_assoc] using hp
  by_cases hs : Real.sin theta = 0
  · have hc : Real.cos theta = 1 ∨ Real.cos theta = -1 := by
      have he : Real.cos theta^2=1^2 := by nlinarith [Real.sin_sq_add_cos_sq theta]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp he
    rcases hc with hc | hc
    · apply Or.inr ∘ Or.inr
      rw [hre,hwr,hzr,hzi,hc,hs]
      simpa only [mul_one,mul_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,
        AffineMap.lineMap_apply_module,smul_eq_mul] using (convex_Ioo l₁ u₁).lineMap_mem hud huc s.property
    · apply Or.inr ∘ Or.inl
      rw [hre,hwr,hzr,hzi,hc,hs]
      simpa only [mul_neg_one,mul_zero,zero_pow (by decide : 2 ≠ 0),sub_zero,← sub_eq_add_neg,
        AffineMap.lineMap_apply_module,smul_eq_mul] using (convex_Ioo l₀ u₀).lineMap_mem hld hlc s.property
  · exact Or.inl (by rw [him];exact mul_ne_zero hs hcoef.ne')

theorem circleIntegral_squared_pullback_eq_circle_of_real_bands
    (f : ℂ → ℂ) (D : Set ℂ) (d R c r l₀ u₀ l₁ u₁ : ℝ)
    (hR : 0 < R) (hr : 0 < r) (hrc : r < c)
    (hld : d-R ∈ Ioo l₀ u₀) (hlc : (c-r)^2 ∈ Ioo l₀ u₀)
    (hud : d+R ∈ Ioo l₁ u₁) (huc : (c+r)^2 ∈ Ioo l₁ u₁)
    (hD : ∀ z : ℂ, z.im ≠ 0 ∨ z.re ∈ Ioo l₀ u₀ ∨ z.re ∈ Ioo l₁ u₁ → z ∈ D)
    (hf : AnalyticOnNhd ℂ f D) :
    (∮ z in C((c : ℂ),r), f (z^2)*(2*z)) = ∮ z in C((d : ℂ),R), f z := by
  let gamma := (circlePath (c : ℂ) r).map (continuous_id.pow 2)
  let H := ContinuousMap.Homotopy.affine (circlePath (d : ℂ) R : C(I,ℂ)) (gamma : C(I,ℂ))
  have hmem (s t : I) : H (s,t) ∈ D := by
    apply hD
    rw [ContinuousMap.Homotopy.affine_apply]
    exact circle_squaredCircle_affine_mem_real_bands d R c r l₀ u₀ l₁ u₁ hR hr hrc
      hld hlc hud huc s ((2*Real.pi)*(t : ℝ))
  have hclosed : IsClosed (range H) := (isCompact_range H.continuous).isClosed
  have heq := curveIntegral_eq_of_holomorphic_homotopy f H affineHomotopy_loop
    (t := range H) (fun s _ t _ => mem_range_self (s,t))
    (by
      rw [hclosed.closure_eq]
      rintro z ⟨⟨s,t⟩,rfl⟩
      exact (hf _ (hmem s t)).differentiableAt)
    (affineHomotopy_contDiffOn (circlePath_contDiffOn _ _) (squaredCirclePath_contDiffOn _ _))
  have hsq (z : ℂ) : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hp := (holomorphicPathPullback_integral_and_integrability f
    (fun z => f (z^2)*(2*z)) (fun z : ℂ => z^2) (fun z : ℂ => 2*z) (continuous_id.pow 2)
    (circlePath (c : ℂ) r) ((circlePath_contDiffOn _ _).of_le (by norm_num))
    (fun _ _ => hsq _) (fun _ _ => rfl)).2
  rw [curveIntegral_circlePath] at hp heq
  exact hp.symm.trans heq.symm

end NLS.ComplexAnalysis
