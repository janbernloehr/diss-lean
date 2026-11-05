import NLS.ComplexAnalysis.NativeCircleTransforms
import NLS.ComplexAnalysis.QuadraticCauchyEquation

/-!
# Cauchy projection of a Banach-valued quadratic equation

The projected function is strongly analytic by its Bochner integral
construction. Scalar observations identify its quadratic differential equation.
-/

noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis
variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

theorem nativeCircleCauchyTransform_quadratic_equation
    (F G : ℂ × A → B) (τ d : A → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (sphere c R ×ˢ V))
    (hG : AnalyticOnNhd ℂ G (closedBall c R ×ˢ V))
    (heq : ∀ p ∈ V, ∀ w ∈ sphere c R,
      quadraticRootPolynomial (τ p) (d p) w • deriv (fun v => F (v,p)) w +
        (w-τ p) • F (w,p) = G (w,p))
    (p : A) (hp : p ∈ V) (z : ℂ) (hz : z ∈ ball c R) :
    quadraticRootPolynomial (τ p) (d p) z •
        deriv (fun v => nativeCircleCauchyTransform F c R (v,p)) z +
      (z-τ p) • nativeCircleCauchyTransform F c R (z,p) = G (z,p) := by
  have hslice : AnalyticOnNhd ℂ (fun w => F (w,p)) (sphere c R) := by
    intro w hw
    exact (hF (w,p) ⟨hw,hp⟩).comp (f := fun w : ℂ => (w,p))
      (analyticAt_id.prod analyticAt_const)
  have hH : AnalyticOnNhd ℂ (fun v => nativeCircleCauchyTransform F c R (v,p))
      (sphere c R)ᶜ := by
    intro w hw
    exact (analyticOnNhd_nativeCircleCauchyTransform F c R hR.le V hV hF
      (w,p) ⟨hw,hp⟩).comp (f := fun w : ℂ => (w,p))
        (analyticAt_id.prod analyticAt_const)
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
  intro L
  have hmap (w : ℂ) (hw : w ∉ sphere c R) :=
    map_nativeCircleCauchyTransform L F c R hR.le p hslice.continuousOn w hw
  have hzn : z ∉ sphere c R := fun hs => sphere_disjoint_ball.le_bot ⟨hs,hz⟩
  have hd := L.hasFDerivAt.comp_hasDerivAt z (hH z hzn).differentiableAt.hasDerivAt
  have hds : HasDerivAt (circleCauchyTransform (fun w => L (F (w,p))) c R)
      (L (deriv (fun v => nativeCircleCauchyTransform F c R (v,p)) z)) z := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [isClosed_sphere.isOpen_compl.mem_nhds hzn] with w hw
    exact (hmap w hw).symm
  rw [map_add, map_smul, map_smul, hmap z hzn, ← hds.deriv]
  apply circleCauchyTransform_quadratic_equation (fun w => L (F (w,p)))
    (fun w => L (G (w,p))) (τ p) (d p) c R hR
  · intro w hw
    exact (L.analyticAt (F (w,p))).comp (f := fun v : ℂ => F (v,p)) (hslice w hw)
  · intro w hw
    exact (L.analyticAt (G (w,p))).comp (f := fun v : ℂ => G (v,p))
      ((hG (w,p) ⟨hw,hp⟩).comp (f := fun v : ℂ => (v,p))
        (analyticAt_id.prod analyticAt_const))
  · intro w hw
    have hdF := L.hasFDerivAt.comp_hasDerivAt w (hslice w hw).differentiableAt.hasDerivAt
    change HasDerivAt (fun v => L (F (v,p))) _ w at hdF
    have hm := congrArg L (heq p hp w hw)
    rw [hdF.deriv]
    simpa only [map_add, map_smul, smul_eq_mul] using hm
  · exact hz

end NLS.ComplexAnalysis
