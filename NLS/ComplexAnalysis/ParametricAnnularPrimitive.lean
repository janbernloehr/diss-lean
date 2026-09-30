import NLS.ComplexAnalysis.ParametricCircleTransforms
import NLS.ComplexAnalysis.ParametricConvexPrimitive

/-!
# A jointly analytic primitive on a zero-period annulus

An explicit primitive of the outer Cauchy transform plus the normalized
inner logarithmic transform works on the entire annulus. Subtracting its
value at a fixed regular anchor preserves joint analyticity and fixes the
constant at every source, including sources where an enclosed gap collapses.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def parametricAnnularPrimitive (F : ℂ × A → ℂ) (c : ℂ) (r R : ℝ) :
    ℂ × A → ℂ :=
  fun x => parametricConvexPrimitive (parametricCircleCauchyTransform F c R) c x +
    parametricCircleLogarithmicPrimitive F c r x

def parametricAnnularPrimitiveAtAnchor
    (F : ℂ × A → ℂ) (c : ℂ) (r R : ℝ) (z₀ : ℂ) : ℂ × A → ℂ :=
  fun x => parametricAnnularPrimitive F c r R x -
    parametricAnnularPrimitive F c r R (z₀,x.2)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
@[simp] theorem parametricAnnularPrimitiveAtAnchor_anchor
    (F : ℂ × A → ℂ) (c : ℂ) (r R : ℝ) (z₀ : ℂ) (a : A) :
    parametricAnnularPrimitiveAtAnchor F c r R z₀ (z₀,a) = 0 := sub_self _

private theorem annulus_outer_circle_subset (c : ℂ) (r R : ℝ) (hrR : r ≤ R) :
    sphere c R ⊆ closedBall c R \ ball c r := by
  intro z hz
  refine ⟨sphere_subset_closedBall hz,?_⟩
  intro hzr
  have hdist := mem_sphere.mp hz
  have hlt := mem_ball.mp hzr
  linarith

private theorem annulus_inner_circle_subset (c : ℂ) (r R : ℝ) (hrR : r ≤ R) :
    sphere c r ⊆ closedBall c R \ ball c r := by
  intro z hz
  exact ⟨mem_closedBall.mpr ((mem_sphere.mp hz).le.trans hrR),
    fun h => sphere_disjoint_ball.le_bot ⟨hz,h⟩⟩

/-- No source-dependent primitive is supplied: both summands are explicit
fixed-circle integrals of the original density. -/
theorem analyticOnNhd_parametricAnnularPrimitive
    (F : ℂ × A → ℂ) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F ((closedBall c R \ ball c r) ×ˢ V)) :
    AnalyticOnNhd ℂ (parametricAnnularPrimitive F c r R)
      ((ball c R \ closedBall c r) ×ˢ V) := by
  have houter : AnalyticOnNhd ℂ F (sphere c R ×ˢ V) :=
    hF.mono (prod_mono (annulus_outer_circle_subset c r R hrR.le) Subset.rfl)
  have hinner : AnalyticOnNhd ℂ F (sphere c r ×ˢ V) :=
    hF.mono (prod_mono (annulus_inner_circle_subset c r R hrR.le) Subset.rfl)
  have hC : AnalyticOnNhd ℂ (parametricCircleCauchyTransform F c R) (ball c R ×ˢ V) :=
    (analyticOnNhd_parametricCircleCauchyTransform F c R (hr.trans hrR).le V hV houter).mono
      (prod_mono (fun _ hz hs => sphere_disjoint_ball.le_bot ⟨hs,hz⟩) Subset.rfl)
  have hP := analyticOnNhd_parametricConvexPrimitive _ _ V c isOpen_ball (convex_ball c R)
    hV (mem_ball_self (hr.trans hrR)) hC
  have hL := analyticOnNhd_parametricCircleLogarithmicPrimitive F c r hr.le V hV hinner
  intro x hx
  exact (hP x ⟨hx.1.1,hx.2⟩).add (hL x ⟨hx.1.2,hx.2⟩)

/-- Each spectral slice has the original density as derivative as soon as
its inner period vanishes. Arbitrary winding around the hole is allowed. -/
theorem hasDerivAt_parametricAnnularPrimitive
    (F : ℂ × A → ℂ) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F ((closedBall c R \ ball c r) ×ˢ V))
    (a : A) (ha : a ∈ V) (hperiod : (∮ w in C(c,r), F (w,a)) = 0)
    (z : ℂ) (hz : z ∈ ball c R \ closedBall c r) :
    HasDerivAt (fun v => parametricAnnularPrimitive F c r R (v,a)) (F (z,a)) z := by
  have houter : AnalyticOnNhd ℂ F (sphere c R ×ˢ V) :=
    hF.mono (prod_mono (annulus_outer_circle_subset c r R hrR.le) Subset.rfl)
  have hC : AnalyticOnNhd ℂ (parametricCircleCauchyTransform F c R) (ball c R ×ˢ V) :=
    (analyticOnNhd_parametricCircleCauchyTransform F c R (hr.trans hrR).le V hV houter).mono
      (prod_mono (fun _ hz hs => sphere_disjoint_ball.le_bot ⟨hs,hz⟩) Subset.rfl)
  have hslice : AnalyticOnNhd ℂ (fun w => F (w,a)) (closedBall c R \ ball c r) := by
    intro w hw
    exact (hF (w,a) ⟨hw,ha⟩).comp (f := fun w : ℂ => (w,a))
      (analyticAt_id.prod analyticAt_const)
  have hd := (hasDerivAt_parametricConvexPrimitive _ _ V c isOpen_ball (convex_ball c R)
    (mem_ball_self (hr.trans hrR)) hC a ha z hz.1).add
    (hasDerivAt_parametricCircleLogarithmicPrimitive F c r hr.le a
      (hslice.mono (annulus_inner_circle_subset c r R hrR.le)) hperiod z hz.2)
  have heq := circleCauchyTransform_outer_sub_inner (fun w => F (w,a)) c r R hr hrR.le hslice z hz
  convert hd using 1 <;> try rfl
  simpa only [parametricCircleCauchyTransform,sub_eq_add_neg] using heq.symm

/-- Normalizing at a fixed point of the annulus fixes the source-dependent
constant without sacrificing joint analyticity. -/
theorem analyticOnNhd_parametricAnnularPrimitiveAtAnchor
    (F : ℂ × A → ℂ) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F ((closedBall c R \ ball c r) ×ˢ V))
    (z₀ : ℂ) (hz₀ : z₀ ∈ ball c R \ closedBall c r) :
    AnalyticOnNhd ℂ (parametricAnnularPrimitiveAtAnchor F c r R z₀)
      ((ball c R \ closedBall c r) ×ˢ V) := by
  have hP := analyticOnNhd_parametricAnnularPrimitive F c r R hr hrR V hV hF
  intro x hx
  exact (hP x hx).sub ((hP (z₀,x.2) ⟨hz₀,hx.2⟩).comp
    (f := fun x : ℂ × A => (z₀,x.2)) (analyticAt_const.prod analyticAt_snd))

theorem hasDerivAt_parametricAnnularPrimitiveAtAnchor
    (F : ℂ × A → ℂ) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F ((closedBall c R \ ball c r) ×ˢ V))
    (z₀ : ℂ) (a : A) (ha : a ∈ V) (hperiod : (∮ w in C(c,r), F (w,a)) = 0)
    (z : ℂ) (hz : z ∈ ball c R \ closedBall c r) :
    HasDerivAt (fun v => parametricAnnularPrimitiveAtAnchor F c r R z₀ (v,a)) (F (z,a)) z := by
  exact (hasDerivAt_parametricAnnularPrimitive F c r R hr hrR V hV hF a ha hperiod z hz).sub_const
    (parametricAnnularPrimitive F c r R (z₀,a))

end NLS.ComplexAnalysis
