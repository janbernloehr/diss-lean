import NLS.ComplexAnalysis.PiecewiseLoopPullback

/-! Vertical compression gives actual smooth thin comparison ellipses.
An affine homotopy fixes real projections and multiplies imaginary
parts by a positive number, so winding about interior real points is one. -/
noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

def verticalScale (s : ℝ) (z : ℂ) : ℂ := ⟨z.re,s*z.im⟩

theorem contDiff_verticalScale (s : ℝ) : ContDiff ℝ 2 (verticalScale s) := by
  have he : verticalScale s = (fun z : ℂ => (z.re:ℂ)+Complex.I*(s*z.im)) := by
    funext z
    apply Complex.ext <;> simp [verticalScale]
  rw [he]
  have hre : ContDiff ℝ 2 (fun z : ℂ => (z.re:ℂ)) := by
    simpa only [Function.comp_def,Complex.ofRealCLM_apply,Complex.reCLM_apply] using
      Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff
  have him : ContDiff ℝ 2 (fun z : ℂ => (z.im:ℂ)) := by
    simpa only [Function.comp_def,Complex.ofRealCLM_apply,Complex.imCLM_apply] using
      Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff
  exact hre.add (contDiff_const.mul (contDiff_const.mul him))

def ellipsePath (c R s : ℝ) :=
  (circlePath (c:ℂ) R).map (contDiff_verticalScale s).continuous

theorem ellipsePath_contDiffOn (c R s : ℝ) :
    ContDiffOn ℝ 2 (ellipsePath c R s).extend (Icc 0 1) :=
  (contDiff_verticalScale s).comp_contDiffOn (circlePath_contDiffOn (c:ℂ) R)

def ellipseLoop (c R s : ℝ) : PiecewiseC1Loop :=
  PiecewiseC1Loop.ofPath (ellipsePath c R s) ((ellipsePath_contDiffOn c R s).of_le (by norm_num))

theorem affine_verticalScale_ne_real (s t : ℝ) (hs : 0 < s) (ht : t ∈ Icc (0:ℝ) 1)
    (z : ℂ) (a : ℝ) (hz : z ≠ (a:ℂ)) :
    (1-t) • z+t • verticalScale s z ≠ (a:ℂ) := by
  have hcoef : 0 < (1-t)+t*s := by
    by_cases h : t = 0
    · simp only [h,sub_zero,zero_mul,add_zero]; norm_num
    · have hp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h)
      have hm := mul_pos hp hs
      linarith [ht.2]
  have hre : ((1-t) • z+t • verticalScale s z : ℂ).re = z.re := by
    simp only [Complex.real_smul,add_re,mul_re,Complex.ofReal_re,Complex.ofReal_im,
      verticalScale]
    ring
  have him : ((1-t) • z+t • verticalScale s z : ℂ).im = ((1-t)+t*s)*z.im := by
    simp only [Complex.real_smul,add_im,mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,verticalScale]
    ring
  intro he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  rw [hre,Complex.ofReal_re] at hr
  rw [him,Complex.ofReal_im] at hi
  exact hz (Complex.ext hr ((mul_eq_zero.mp hi).resolve_left hcoef.ne'))

theorem ellipseLoop_winding_one (c R s a : ℝ) (hR : 0 < R) (hs : 0 < s)
    (ha : (a:ℂ) ∈ ball (c:ℂ) R) : (ellipseLoop c R s).windingIntegral (a:ℂ) = 1 := by
  let γ := circlePath (c:ℂ) R
  let η := ellipsePath c R s
  let H := ContinuousMap.Homotopy.affine (γ : C(I,ℂ)) (η : C(I,ℂ))
  have havoid (t u : I) : H (t,u) ≠ (a:ℂ) := by
    have hz : γ u ≠ (a:ℂ) := by
      intro he
      have hmem : γ u ∈ sphere (c:ℂ) R :=
        circleMap_mem_sphere (c:ℂ) hR.le ((2*Real.pi)*(u:ℝ))
      rw [he] at hmem
      exact (mem_ball.mp ha).ne (mem_sphere.mp hmem)
    have he : H (t,u) = (1-(t:ℝ)) • γ u+(t:ℝ) • verticalScale s (γ u) := by
      rw [ContinuousMap.Homotopy.affine_apply]
      change AffineMap.lineMap (γ u) (verticalScale s (γ u)) (t:ℝ) = _
      rw [AffineMap.lineMap_apply_module]
    rw [he]
    exact affine_verticalScale_ne_real s (t:ℝ) hs t.property (γ u) a hz
  have hclosed : IsClosed (range H) := (isCompact_range (map_continuous H)).isClosed
  have hf : ∀ z ∈ closure (range H), DifferentiableAt ℂ (fun w : ℂ => (w-(a:ℂ))⁻¹) z := by
    intro z hz
    rw [hclosed.closure_eq] at hz
    obtain ⟨⟨t,u⟩,rfl⟩ := hz
    exact ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr (havoid t u))).differentiableAt
  have heq := curveIntegral_eq_of_holomorphic_homotopy (fun z : ℂ => (z-(a:ℂ))⁻¹) H
    (affineHomotopy_loop (γ₁ := γ) (γ₂ := η))
    (fun t _ u _ => (show H (t,u) ∈ range H from ⟨(t,u),rfl⟩)) hf
    (affineHomotopy_contDiffOn (circlePath_contDiffOn _ _) (ellipsePath_contDiffOn c R s))
  simp only [ellipseLoop,PiecewiseC1Loop.windingIntegral,PiecewiseC1Loop.normalizedIntegral,PiecewiseC1Loop.integral_ofPath]
  change (2*Real.pi*Complex.I:ℂ)⁻¹*(∫ᶜ z in η, holomorphicOneForm (fun z => (z-(a:ℂ))⁻¹) z) = 1
  rw [← heq,curveIntegral_circlePath,circleIntegral.integral_sub_inv_of_mem_ball ha]
  field_simp

end NLS.ComplexAnalysis
