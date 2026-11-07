import NLS.ComplexAnalysis.ParametricAnnularPrimitive
import NLS.ComplexAnalysis.QuadraticRootPrimitive

/-! Jointly analytic solutions of the quadratic root equation from
literal zero-period annular integrals. The construction divides only
on a fixed enclosing circle and fills the whole interior disc. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def parametricQuadraticCauchySolution (f Q : ℂ × A → ℂ) (c : ℂ) (r R ρ : ℝ) : ℂ × A → ℂ :=
  parametricCircleCauchyTransform (fun t => parametricAnnularPrimitive f c r R t/Q t) c ρ

theorem analyticOnNhd_parametricQuadraticCauchySolution (f Q : ℂ × A → ℂ) (c : ℂ) (r R ρ : ℝ)
    (hr : 0 < r) (hrρ : r < ρ) (hρR : ρ < R) (V : Set A) (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f ((closedBall c R \ ball c r) ×ˢ V))
    (hQ : AnalyticOnNhd ℂ Q ((ball c R \ closedBall c r) ×ˢ V))
    (hQne : ∀ t ∈ (ball c R \ closedBall c r) ×ˢ V, Q t ≠ 0) :
    AnalyticOnNhd ℂ (parametricQuadraticCauchySolution f Q c r R ρ) (ball c ρ ×ˢ V) := by
  have hP := analyticOnNhd_parametricAnnularPrimitive f c r R hr (hrρ.trans hρR) V hV hf
  have hdensity : AnalyticOnNhd ℂ (fun t => parametricAnnularPrimitive f c r R t/Q t) (sphere c ρ ×ˢ V) := by
    intro t ht
    have hz : t.1 ∈ ball c R \ closedBall c r :=
      ⟨mem_ball.mpr ((mem_sphere.mp ht.1).trans_lt hρR),fun hh =>
        (not_le_of_gt hrρ) ((mem_sphere.mp ht.1) ▸ mem_closedBall.mp hh)⟩
    exact (hP t ⟨hz,ht.2⟩).div (hQ t ⟨hz,ht.2⟩) (hQne t ⟨hz,ht.2⟩)
  exact (analyticOnNhd_parametricCircleCauchyTransform _ c ρ (hr.trans hrρ).le V hV hdensity).mono
    (prod_mono (fun _ hz hs => sphere_disjoint_ball.le_bot ⟨hs,hz⟩) Subset.rfl)

theorem parametricQuadraticCauchySolution_equation (f Q g : ℂ × A → ℂ)
    (c τ d : ℂ) (r R ρ : ℝ) (hr : 0 < r) (hrρ : r < ρ) (hρR : ρ < R)
    (V : Set A) (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f ((closedBall c R \ ball c r) ×ˢ V))
    (hQ : AnalyticOnNhd ℂ Q ((ball c R \ closedBall c r) ×ˢ V))
    (a : A) (ha : a ∈ V)
    (hQne : ∀ z ∈ ball c R \ closedBall c r, Q (z,a) ≠ 0)
    (hsq : ∀ z ∈ ball c R \ closedBall c r, Q (z,a)^2 = quadraticRootPolynomial τ d z)
    (hfg : ∀ z ∈ ball c R \ closedBall c r, f (z,a) = g (z,a)/Q (z,a))
    (hg : AnalyticOnNhd ℂ (fun z => g (z,a)) (closedBall c ρ))
    (hperiod : (∮ z in C(c,r), f (z,a)) = 0) (z : ℂ) (hz : z ∈ ball c ρ) :
    quadraticRootPolynomial τ d z*deriv (fun w => parametricQuadraticCauchySolution f Q c r R ρ (w,a)) z+
      (z-τ)*parametricQuadraticCauchySolution f Q c r R ρ (z,a) = g (z,a) := by
  let P : ℂ → ℂ := fun w => parametricAnnularPrimitive f c r R (w,a)
  let B : ℂ → ℂ := fun w => Q (w,a)
  let H : ℂ → ℂ := fun w => P w/B w
  let U := ball c R \ closedBall c r
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_closedBall
  have hcircle (w : ℂ) (hw : w ∈ sphere c ρ) : w ∈ U :=
    ⟨mem_ball.mpr ((mem_sphere.mp hw).trans_lt hρR),fun hh =>
      (not_le_of_gt hrρ) ((mem_sphere.mp hw) ▸ mem_closedBall.mp hh)⟩
  have hBa (w : ℂ) (hw : w ∈ U) : AnalyticAt ℂ B w :=
    (hQ (w,a) ⟨hw,ha⟩).comp (f := fun t : ℂ => (t,a)) (analyticAt_id.prod analyticAt_const)
  have hPd (w : ℂ) (hw : w ∈ U) : HasDerivAt P (g (w,a)/B w) w := by
    rw [← hfg w hw]
    exact hasDerivAt_parametricAnnularPrimitive f c r R hr (hrρ.trans hρR) V hV hf a ha hperiod w hw
  have hPa : AnalyticOnNhd ℂ P U := by
    intro w hw
    exact (analyticOnNhd_parametricAnnularPrimitive f c r R hr (hrρ.trans hρR) V hV hf (w,a) ⟨hw,ha⟩).comp
      (f := fun t : ℂ => (t,a)) (analyticAt_id.prod analyticAt_const)
  have hH : AnalyticOnNhd ℂ H (sphere c ρ) := fun w hw =>
    (hPa w (hcircle w hw)).div (hBa w (hcircle w hw)) (hQne w (hcircle w hw))
  have heq (w : ℂ) (hw : w ∈ sphere c ρ) :
      quadraticRootPolynomial τ d w*deriv H w+(w-τ)*H w = g (w,a) := by
    have hwU := hcircle w hw
    have hsqNear : (fun t => B t^2) =ᶠ[𝓝 w] quadraticRootPolynomial τ d := by
      filter_upwards [hU.mem_nhds hwU] with t ht
      exact hsq t ht
    have hBd := hasDerivAt_root_of_sq_eq_quadratic B τ d w (hBa w hwU) (hQne w hwU) hsqNear
    have hHd := (hPd w hwU).fun_div hBd (hQne w hwU)
    rw [(hsq w hwU).symm,hHd.deriv]
    dsimp only [H,B]
    field_simp [hQne w hwU]
    ring
  exact circleCauchyTransform_quadratic_equation H (fun w => g (w,a)) τ d c ρ (hr.trans hrρ) hH hg heq z hz

end NLS.ComplexAnalysis
