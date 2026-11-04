import NLS.ComplexAnalysis.ParametricConvexPrimitive
import NLS.ComplexAnalysis.PolygonalEndpointIntegral

/-! The existing jointly analytic convex primitive is the ACTUAL
segment integral. Every smooth or polygonal path in its convex chart
evaluates to its endpoint difference. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped unitInterval
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem parametricConvexPrimitive_eq_curveIntegral (F : ℂ × A → ℂ) (a E : ℂ) (q : A) :
    parametricConvexPrimitive F a (E,q) =
      ∫ᶜ z in Path.segment a E, holomorphicOneForm (fun w => F (w,q)) z := by
  rw [parametricConvexPrimitive,curveIntegral_segment]
  apply intervalIntegral.integral_congr
  intro u _
  have hline : AffineMap.lineMap a E u = a+(u:ℂ)*(E-a) := by
    rw [AffineMap.lineMap_apply_module']
    simp only [Complex.real_smul]
    ring
  dsimp only
  rw [hline,holomorphicOneForm_apply]
  ring

theorem curveIntegral_eq_parametricConvexPrimitive_sub (F : ℂ × A → ℂ)
    (U : Set ℂ) (V : Set A) (c : ℂ) (hU : IsOpen U) (hconv : Convex ℝ U) (hc : c ∈ U)
    (hF : AnalyticOnNhd ℂ F (U ×ˢ V)) (q : A) (hq : q ∈ V)
    {a b : ℂ} (γ : Path a b) (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hinside : ∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ U) :
    (∫ᶜ z in γ, holomorphicOneForm (fun E => F (E,q)) z) =
      parametricConvexPrimitive F c (b,q)-parametricConvexPrimitive F c (a,q) := by
  have hderiv := hasDerivAt_parametricConvexPrimitive F U V c hU hconv hc hF q hq
  have hslice : AnalyticOnNhd ℂ (fun E => F (E,q)) U := by
    intro E hE
    exact (hF (E,q) ⟨hE,hq⟩).comp (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)
  have hcont : ContinuousOn (fun E => F (E,q)) U := hslice.continuousOn
  have hω : ContinuousOn (holomorphicOneForm (fun E => F (E,q))) U := hcont.smul continuousOn_const
  have hrange : ∀ t : I, γ t ∈ U := by
    intro t
    simpa only [Path.extend_apply _ t.property] using hinside t t.property
  exact curveIntegral_eq_sub_of_primitive _ _ U hderiv γ hγ hinside
    (hω.curveIntegrable_of_contDiffOn hγ hrange)

theorem polygonalIntegral_eq_parametricConvexPrimitive_sub (F : ℂ × A → ℂ)
    (U : Set ℂ) (V : Set A) (c : ℂ) (hU : IsOpen U) (hconv : Convex ℝ U) (hc : c ∈ U)
    (hF : AnalyticOnNhd ℂ F (U ×ˢ V)) (q : A) (hq : q ∈ V)
    (a b : ℂ) (ha : a ∈ U) (hb : b ∈ U) :
    polygonalIntegral (fun E => F (E,q)) U a b =
      parametricConvexPrimitive F c (b,q)-parametricConvexPrimitive F c (a,q) := by
  have hderiv := hasDerivAt_parametricConvexPrimitive F U V c hU hconv hc hF q hq
  have hslice : AnalyticOnNhd ℂ (fun E => F (E,q)) U := by
    intro E hE
    exact (hF (E,q) ⟨hE,hq⟩).comp (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)
  have hcont : ContinuousOn (fun E => F (E,q)) U := hslice.continuousOn
  exact polygonalIntegral_eq_sub _ _ U hU hconv.isPreconnected hcont hderiv a b ha hb

end NLS.ComplexAnalysis
