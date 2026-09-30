import NLS.ComplexAnalysis.CircleLogarithmicPrimitive

/-!
# Holomorphic primitives on a zero-period annulus

Annular Cauchy decomposition splits the function into an analytic
outer-disc term and an exterior inner-circle term. The logarithmic
primitive of the latter cancels the only period. This constructs a
primitive on the entire annulus, and proves path independence for
arbitrary C¹ paths there without a homotopy assumption.
-/

noncomputable section
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

theorem exists_primitive_on_annulus_of_zero_period
    (f : ℂ → ℂ) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R \ ball c r))
    (hperiod : (∮ w in C(c,r), f w) = 0) :
    ∃ F : ℂ → ℂ, ∀ z ∈ ball c R \ closedBall c r, HasDerivAt F (f z) z := by
  have houter : sphere c R ⊆ closedBall c R \ ball c r := by
    intro z hz
    refine ⟨sphere_subset_closedBall hz,?_⟩
    intro hzr
    have hdist := mem_sphere.mp hz
    have hlt := mem_ball.mp hzr
    linarith
  have hinner : sphere c r ⊆ closedBall c R \ ball c r := by
    intro z hz
    exact ⟨mem_closedBall.mpr ((mem_sphere.mp hz).le.trans hrR.le),
      fun h => sphere_disjoint_ball.le_bot ⟨hz,h⟩⟩
  have hC : AnalyticOnNhd ℂ (circleCauchyTransform f c R) (ball c R) :=
    (analyticOnNhd_circleCauchyTransform f c R (hr.trans hrR).le (hf.mono houter)).mono
      (fun _ hz hs => sphere_disjoint_ball.le_bot ⟨hs,hz⟩)
  obtain ⟨G,hG⟩ := exists_primitive_on_convex _ (ball c R) (convex_ball _ _) isOpen_ball hC.differentiableOn
  refine ⟨fun z => G z+circleLogarithmicPrimitive f c r z,?_⟩
  intro z hz
  have hd := (hG z hz.1).add
    (hasDerivAt_circleLogarithmicPrimitive f c r hr.le (hf.mono hinner) hperiod z hz.2)
  have heq := circleCauchyTransform_outer_sub_inner f c r R hr hrR.le hf z hz
  convert hd using 1 <;> try rfl
  simpa only [sub_eq_add_neg] using heq.symm

/-- Whole-annulus path independence includes paths with arbitrary
winding around the hole; integrability follows from C¹ regularity. -/
theorem curveIntegral_eq_of_annular_paths_zero_period
    (f : ℂ → ℂ) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R \ ball c r))
    (hperiod : (∮ w in C(c,r), f w) = 0)
    {a b : ℂ} (γ₁ γ₂ : Path a b)
    (hγ₁ : ContDiffOn ℝ 1 γ₁.extend (Icc 0 1)) (hγ₂ : ContDiffOn ℝ 1 γ₂.extend (Icc 0 1))
    (hγ₁A : ∀ t : I, γ₁ t ∈ ball c R \ closedBall c r)
    (hγ₂A : ∀ t : I, γ₂ t ∈ ball c R \ closedBall c r) :
    (∫ᶜ z in γ₁, holomorphicOneForm f z) = ∫ᶜ z in γ₂, holomorphicOneForm f z := by
  let A := ball c R \ closedBall c r
  have hA : A ⊆ closedBall c R \ ball c r := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.1,fun h => hz.2 (ball_subset_closedBall h)⟩
  obtain ⟨F,hF⟩ := exists_primitive_on_annulus_of_zero_period f c r R hr hrR hf hperiod
  have hω : ContinuousOn (holomorphicOneForm f) A :=
    (hf.continuousOn.mono hA).smul continuousOn_const
  rw [curveIntegral_eq_sub_of_primitive f F A hF γ₁ hγ₁
    (fun t ht => by simpa only [Path.extend_apply γ₁ ht] using hγ₁A ⟨t,ht⟩)
    (hω.curveIntegrable_of_contDiffOn hγ₁ hγ₁A),
    curveIntegral_eq_sub_of_primitive f F A hF γ₂ hγ₂
    (fun t ht => by simpa only [Path.extend_apply γ₂ ht] using hγ₂A ⟨t,ht⟩)
    (hω.curveIntegrable_of_contDiffOn hγ₂ hγ₂A)]

end NLS.ComplexAnalysis
