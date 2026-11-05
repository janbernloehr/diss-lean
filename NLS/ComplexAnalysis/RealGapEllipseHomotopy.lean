import NLS.ComplexAnalysis.RealGapEllipse

/-! # Deforming a clockwise ellipse to its enclosing circle -/

noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

/-- The reversed circle path has the negative angular parameter. -/
theorem circlePath_symm_apply (c : ℂ) (r : ℝ) (u : I) :
    (circlePath c r).symm u = circleMap c r (-((2 * Real.pi) * (u : ℝ))) := by
  change circleMap c r ((2 * Real.pi) * (1 - (u : ℝ))) = _
  calc
    _ = circleMap c r (-((2 * Real.pi) * (u : ℝ)) + 2 * Real.pi) := by
      congr 1
      ring
    _ = _ := periodic_circleMap c r _

theorem circlePath_symm_contDiffOn (c : ℂ) (r : ℝ) :
    ContDiffOn ℝ 2 (circlePath c r).symm.extend (Icc 0 1) := by
  have hmap : MapsTo (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  simpa only [Path.extend_symm, Function.comp_def] using
    (circlePath_contDiffOn c r).comp
      (show ContDiffOn ℝ 2 (fun t : ℝ => 1 - t) (Icc 0 1) from by fun_prop) hmap

private theorem circleMap_negative_re (c r θ : ℝ) :
    (circleMap (c : ℂ) r (-θ)).re = c + r * Real.cos θ := by
  unfold circleMap
  rw [exp_mul_I]
  simp only [add_re, mul_re, ofReal_re, ofReal_im,
    zero_mul, sub_zero, cos_ofReal_re, sin_ofReal_im,
    I_re, I_im, mul_one, mul_zero, add_zero, sin_ofReal_re,
    Real.cos_neg, Real.sin_neg]

private theorem circleMap_negative_im (c r θ : ℝ) :
    (circleMap (c : ℂ) r (-θ)).im = -r * Real.sin θ := by
  unfold circleMap
  rw [exp_mul_I]
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
    cos_ofReal_im, sin_ofReal_re, sin_ofReal_im, I_re, I_im, mul_one, mul_zero,
    Real.sin_neg]
  ring

/-- The affine homotopy keeps the real projection fixed and increases
only the vertical semiaxis. -/
theorem realGapEllipse_affine_coordinates (c d ε : ℝ) (s u : I) :
    let z := (ContinuousMap.Homotopy.affine
      (realGapEllipsePath c d ε : C(I, ℂ))
      ((circlePath (c : ℂ) (d + ε)).symm : C(I, ℂ))) (s, u)
    z.re = c + (d + ε) * Real.cos ((2 * Real.pi) * (u : ℝ)) ∧
      z.im = -(ε + (s : ℝ) * d) * Real.sin ((2 * Real.pi) * (u : ℝ)) := by
  dsimp only
  rw [ContinuousMap.Homotopy.affine_apply]
  change (AffineMap.lineMap (realGapEllipse c d ε ((2 * Real.pi) * (u : ℝ)))
    ((circlePath (c : ℂ) (d + ε)).symm u) (s : ℝ)).re = _ ∧
    (AffineMap.lineMap (realGapEllipse c d ε ((2 * Real.pi) * (u : ℝ)))
      ((circlePath (c : ℂ) (d + ε)).symm u) (s : ℝ)).im = _
  rw [circlePath_symm_apply]
  simp only [AffineMap.lineMap_apply_module, Complex.real_smul,
    add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im,
    zero_mul, sub_zero, add_zero, realGapEllipse_re, realGapEllipse_im,
    circleMap_negative_re, circleMap_negative_im]
  constructor <;> ring

/-- Every intermediate loop stays inside the enclosing filled circle. -/
theorem realGapEllipse_affine_mem_closedBall (c d ε : ℝ)
    (hd : 0 ≤ d) (hε : 0 ≤ ε) (s u : I) :
    (ContinuousMap.Homotopy.affine
      (realGapEllipsePath c d ε : C(I, ℂ))
      ((circlePath (c : ℂ) (d + ε)).symm : C(I, ℂ))) (s, u) ∈
        closedBall (c : ℂ) (d + ε) := by
  rw [ContinuousMap.Homotopy.affine_apply]
  apply (convex_closedBall (c : ℂ) (d + ε)).lineMap_mem
    (realGapEllipse_mem_closedBall c d ε _ hd hε) _ s.property
  change (circlePath (c : ℂ) (d + ε)).symm u ∈ _
  rw [circlePath_symm_apply]
  exact circleMap_mem_closedBall _ (add_nonneg hd hε) _

/-- Every intermediate loop avoids the full real gap, including its endpoints. -/
theorem realGapEllipse_affine_not_mem_segment (c d ε : ℝ)
    (hd : 0 < d) (hε : 0 < ε) (s u : I) :
    (ContinuousMap.Homotopy.affine
      (realGapEllipsePath c d ε : C(I, ℂ))
      ((circlePath (c : ℂ) (d + ε)).symm : C(I, ℂ))) (s, u) ∉
        segment ℝ ((c - d : ℝ) : ℂ) ((c + d : ℝ) : ℂ) := by
  intro hz
  obtain ⟨hre, him⟩ := realGapEllipse_affine_coordinates c d ε s u
  have hz0 := im_eq_zero_of_mem_real_segment (c - d) (c + d) _ hz
  rw [him] at hz0
  have hb : 0 < ε + (s : ℝ) * d := by
    nlinarith [mul_nonneg s.property.1 hd.le]
  have hsin : Real.sin ((2 * Real.pi) * (u : ℝ)) = 0 :=
    (mul_eq_zero.mp hz0).resolve_left (neg_ne_zero.mpr hb.ne')
  have hr := re_mem_Icc_of_mem_real_segment (c - d) (c + d) (by linarith) _ hz
  rw [hre] at hr
  have hc : Real.cos ((2 * Real.pi) * (u : ℝ)) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq ((2 * Real.pi) * (u : ℝ))]
  have hs : ((d + ε) * Real.cos ((2 * Real.pi) * (u : ℝ))) ^ 2 ≤ d ^ 2 :=
    sq_le_sq' (by linarith [hr.1]) (by linarith [hr.2])
  rw [mul_pow, hc, mul_one] at hs
  nlinarith [sq_nonneg ε]

/-- A holomorphic integral on the enclosing disc minus the real gap
equals the negative (clockwise) circle integral. -/
theorem curveIntegral_realGapEllipse_eq_neg_circleIntegral
    (f : ℂ → ℂ) (c d ε R : ℝ) (hd : 0 < d) (hε : 0 < ε)
    (hR : d + ε < R)
    (hf : DifferentiableOn ℂ f
      (ball (c : ℂ) R \ segment ℝ ((c - d : ℝ) : ℂ) ((c + d : ℝ) : ℂ))) :
    (∫ᶜ z in realGapEllipsePath c d ε, holomorphicOneForm f z) =
      -(∮ z in C((c : ℂ), d + ε), f z) := by
  let H := ContinuousMap.Homotopy.affine
    (realGapEllipsePath c d ε : C(I, ℂ))
    ((circlePath (c : ℂ) (d + ε)).symm : C(I, ℂ))
  have hmem (s u : I) : H (s, u) ∈
      ball (c : ℂ) R \ segment ℝ ((c - d : ℝ) : ℂ) ((c + d : ℝ) : ℂ) := by
    exact ⟨lt_of_le_of_lt
      (realGapEllipse_affine_mem_closedBall c d ε hd.le hε.le s u) hR,
      realGapEllipse_affine_not_mem_segment c d ε hd hε s u⟩
  have hclosed : IsClosed (range H) := isCompact_range H.continuous |>.isClosed
  have hsegment : IsClosed (segment ℝ ((c - d : ℝ) : ℂ) ((c + d : ℝ) : ℂ)) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  have hopen : IsOpen
      (ball (c : ℂ) R \ segment ℝ ((c - d : ℝ) : ℂ) ((c + d : ℝ) : ℂ)) :=
    isOpen_ball.sdiff hsegment
  have heq := curveIntegral_eq_of_holomorphic_homotopy f H
    (affineHomotopy_loop) (t := range H)
    (fun s _ u _ => mem_range_self (s, u))
    (by
      rw [hclosed.closure_eq]
      rintro z ⟨⟨s, u⟩, rfl⟩
      exact hf.differentiableAt (hopen.mem_nhds (hmem s u)))
    (affineHomotopy_contDiffOn (realGapEllipsePath_contDiffOn c d ε)
      (circlePath_symm_contDiffOn (c : ℂ) (d + ε)))
  simpa only [curveIntegral_symm, curveIntegral_circlePath] using heq

end NLS.ComplexAnalysis
