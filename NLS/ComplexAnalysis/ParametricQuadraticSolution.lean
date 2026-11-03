import NLS.ComplexAnalysis.ParametricAnnularPrimitive
import NLS.ComplexAnalysis.QuadraticCauchyEquation
import NLS.ComplexAnalysis.QuadraticRootPrimitive

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem exists_analytic_parametric_quadratic_solution_of_zero_period
    (g Q : ℂ × A → ℂ) (τ s : A → ℂ) (c : ℂ) (r ρ R : ℝ)
    (hr : 0 < r) (hrρ : r < ρ) (hρR : ρ < R) (V : Set A) (hV : IsOpen V)
    (hg : AnalyticOnNhd ℂ g (closedBall c R ×ˢ V))
    (hQ : AnalyticOnNhd ℂ Q ((closedBall c R \ ball c r) ×ˢ V))
    (hne : ∀ p ∈ V, ∀ z ∈ closedBall c R \ ball c r, Q (z,p) ≠ 0)
    (hsq : ∀ p ∈ V, ∀ z ∈ closedBall c R \ ball c r,
      Q (z,p)^2 = quadraticRootPolynomial (τ p) (s p) z)
    (hperiod : ∀ p ∈ V, (∮ z in C(c,r), g (z,p)/Q (z,p)) = 0) :
    ∃ H : ℂ × A → ℂ, AnalyticOnNhd ℂ H (ball c ρ ×ˢ V) ∧
      ∀ p ∈ V, ∀ z ∈ ball c ρ,
        quadraticRootPolynomial (τ p) (s p) z*deriv (fun w => H (w,p)) z +
          (z-τ p)*H (z,p) = g (z,p) := by
  let K := closedBall c R \ ball c r
  let D : ℂ × A → ℂ := fun t => g t/Q t
  have hD : AnalyticOnNhd ℂ D (K ×ˢ V) := by
    intro t ht
    exact (hg t ⟨ht.1.1,ht.2⟩).div (hQ t ht) (hne t.2 ht.2 t.1 ht.1)
  let F := parametricAnnularPrimitive D c r R
  have hF : AnalyticOnNhd ℂ F ((ball c R \ closedBall c r) ×ˢ V) :=
    analyticOnNhd_parametricAnnularPrimitive D c r R hr (hrρ.trans hρR) V hV hD
  let f : ℂ × A → ℂ := fun t => F t/Q t
  have hf : AnalyticOnNhd ℂ f ((ball c R \ closedBall c r) ×ˢ V) := by
    intro t ht
    have htK : t.1 ∈ K := ⟨ball_subset_closedBall ht.1.1,fun he => ht.1.2 (ball_subset_closedBall he)⟩
    exact (hF t ht).div (hQ t ⟨htK,ht.2⟩) (hne t.2 ht.2 t.1 htK)
  have hcircle : sphere c ρ ⊆ ball c R \ closedBall c r := by
    intro z hz
    have hd : dist z c = ρ := hz
    exact ⟨by rw [mem_ball,hd];exact hρR,by rw [mem_closedBall,hd];exact not_le.mpr hrρ⟩
  have hfρ : AnalyticOnNhd ℂ f (sphere c ρ ×ˢ V) := hf.mono (prod_mono hcircle Subset.rfl)
  let H := parametricCircleCauchyTransform f c ρ
  have hρ : 0 < ρ := hr.trans hrρ
  have hH : AnalyticOnNhd ℂ H (ball c ρ ×ˢ V) :=
    (analyticOnNhd_parametricCircleCauchyTransform f c ρ hρ.le V hV hfρ).mono
      (prod_mono (fun z hz hs => sphere_disjoint_ball.le_bot ⟨hs,hz⟩) Subset.rfl)
  refine ⟨H,hH,?_⟩
  intro p hp z hz
  have hgslice : AnalyticOnNhd ℂ (fun w => g (w,p)) (closedBall c ρ) := by
    intro w hw
    exact (hg (w,p) ⟨closedBall_subset_closedBall hρR.le hw,hp⟩).comp
      (f := fun w : ℂ => (w,p)) (analyticAt_id.prod analyticAt_const)
  have hfslice : AnalyticOnNhd ℂ (fun w => f (w,p)) (sphere c ρ) := by
    intro w hw
    exact (hfρ (w,p) ⟨hw,hp⟩).comp (f := fun w : ℂ => (w,p)) (analyticAt_id.prod analyticAt_const)
  apply circleCauchyTransform_quadratic_equation (fun w => f (w,p)) (fun w => g (w,p))
    (τ p) (s p) c ρ hρ hfslice hgslice _ z hz
  intro w hw
  have hwA : w ∈ ball c R \ closedBall c r := hcircle hw
  have hwK : w ∈ K := ⟨ball_subset_closedBall hwA.1,fun he => hwA.2 (ball_subset_closedBall he)⟩
  have hQw : AnalyticAt ℂ (fun u => Q (u,p)) w :=
    (hQ (w,p) ⟨hwK,hp⟩).comp (f := fun u : ℂ => (u,p)) (analyticAt_id.prod analyticAt_const)
  have hQn := hne p hp w hwK
  have hQsq : (fun u => Q (u,p)^2) =ᶠ[𝓝 w] quadraticRootPolynomial (τ p) (s p) := by
    filter_upwards [(isOpen_ball.sdiff isClosed_closedBall).mem_nhds hwA] with u hu
    exact hsq p hp u ⟨ball_subset_closedBall hu.1,fun he => hu.2 (ball_subset_closedBall he)⟩
  have hQd := hasDerivAt_root_of_sq_eq_quadratic (fun u => Q (u,p)) (τ p) (s p) w hQw hQn hQsq
  have hFd : HasDerivAt (fun u => F (u,p)) (g (w,p)/Q (w,p)) w :=
    hasDerivAt_parametricAnnularPrimitive D c r R hr (hrρ.trans hρR) V hV hD p hp (hperiod p hp) w hwA
  have hfd := hFd.fun_div hQd hQn
  change HasDerivAt (fun u => f (u,p)) _ w at hfd
  rw [hfd.deriv]
  rw [← hsq p hp w hwK]
  dsimp only [f]
  field_simp
  ring

end NLS.ComplexAnalysis
