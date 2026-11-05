import NLS.ComplexAnalysis.NativeAnnularPrimitive
import NLS.ComplexAnalysis.NativeQuadraticCauchyEquation
import NLS.ComplexAnalysis.QuadraticRootPrimitive
import NLS.ComplexAnalysis.NativeCirclePrimitiveBounds

/-! # A bounded native Banach-valued solution of the quadratic root equation

A genuine zero Bochner period produces a strongly jointly analytic solution
on the filled disc, with a full target-norm bound independent of coordinates.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis

variable {A B : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

theorem exists_bounded_native_quadratic_solution_of_zero_period
    (g : ℂ × A → B) (Q : ℂ × A → ℂ) (τ s : A → ℂ) (c : ℂ) (r ρ R a δ M : ℝ)
    (haρ : a < ρ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hr : 0 < r) (hrρ : r < ρ) (hρR : ρ < R) (V : Set A) (hV : IsOpen V)
    (hg : AnalyticOnNhd ℂ g (closedBall c R ×ˢ V))
    (hQ : AnalyticOnNhd ℂ Q ((closedBall c R \ ball c r) ×ˢ V))
    (hne : ∀ p ∈ V, ∀ z ∈ closedBall c R \ ball c r, Q (z,p) ≠ 0)
    (hsq : ∀ p ∈ V, ∀ z ∈ closedBall c R \ ball c r,
      Q (z,p)^2 = quadraticRootPolynomial (τ p) (s p) z)
    (hperiod : ∀ p ∈ V, (∮ z in C(c,r), (Q (z,p))⁻¹ • g (z,p)) = 0)
    (hQlower : ∀ p ∈ V, ∀ z ∈ sphere c ρ, δ ≤ ‖Q (z,p)‖)
    (hbound : ∀ p ∈ V, ∀ z ∈ sphere c ρ, ‖(Q (z,p))⁻¹ • g (z,p)‖ ≤ M) :
    ∃ H : ℂ × A → B, AnalyticOnNhd ℂ H (ball c ρ ×ˢ V) ∧
      (∀ p ∈ V, ∀ z ∈ ball c ρ,
        quadraticRootPolynomial (τ p) (s p) z • deriv (fun w => H (w,p)) z +
          (z-τ p) • H (z,p) = g (z,p)) ∧
      ∀ p ∈ V, ∀ z ∈ closedBall c a, ‖H (z,p)‖ ≤ Real.pi*ρ^2*M/(δ*(ρ-a)) := by
  let K := closedBall c R \ ball c r
  let D : ℂ × A → B := fun t => (Q t)⁻¹ • g t
  have hD : AnalyticOnNhd ℂ D (K ×ˢ V) := by
    intro t ht
    exact ((hQ t ht).inv (hne t.2 ht.2 t.1 ht.1)).smul (hg t ⟨ht.1.1,ht.2⟩)
  have hρ : 0 < ρ := hr.trans hrρ
  have hanchor : c+(ρ : ℂ) ∈ ball c R \ closedBall c r := by
    have hd : dist (c+(ρ : ℂ)) c=ρ := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_real,Real.norm_eq_abs,abs_of_pos hρ]
    exact ⟨by rw [mem_ball,hd];exact hρR,by rw [mem_closedBall,hd];exact not_le.mpr hrρ⟩
  let F := nativeAnnularPrimitiveAtAnchor D c r R (c+ρ)
  have hF : AnalyticOnNhd ℂ F ((ball c R \ closedBall c r) ×ˢ V) :=
    analyticOnNhd_nativeAnnularPrimitiveAtAnchor D c r R hr (hrρ.trans hρR) V hV hD (c+ρ) hanchor
  let f : ℂ × A → B := fun t => (Q t)⁻¹ • F t
  have hf : AnalyticOnNhd ℂ f ((ball c R \ closedBall c r) ×ˢ V) := by
    intro t ht
    have htK : t.1 ∈ K := ⟨ball_subset_closedBall ht.1.1,fun he => ht.1.2 (ball_subset_closedBall he)⟩
    exact ((hQ t ⟨htK,ht.2⟩).inv (hne t.2 ht.2 t.1 htK)).smul (hF t ht)
  have hcircle : sphere c ρ ⊆ ball c R \ closedBall c r := by
    intro z hz
    have hd : dist z c = ρ := hz
    exact ⟨by rw [mem_ball,hd];exact hρR,by rw [mem_closedBall,hd];exact not_le.mpr hrρ⟩
  have hfρ : AnalyticOnNhd ℂ f (sphere c ρ ×ˢ V) := hf.mono (prod_mono hcircle Subset.rfl)
  let H := nativeCircleCauchyTransform f c ρ
  have hH : AnalyticOnNhd ℂ H (ball c ρ ×ˢ V) :=
    (analyticOnNhd_nativeCircleCauchyTransform f c ρ hρ.le V hV hfρ).mono
      (prod_mono (fun z hz hs => sphere_disjoint_ball.le_bot ⟨hs,hz⟩) Subset.rfl)
  refine ⟨H,hH,?_,?_⟩
  · intro p hp z hz
    apply nativeCircleCauchyTransform_quadratic_equation f g τ s c ρ hρ V hV hfρ
      (hg.mono (prod_mono (closedBall_subset_closedBall hρR.le) Subset.rfl)) _ p hp z hz
    intro p hp w hw
    have hwA : w ∈ ball c R \ closedBall c r := hcircle hw
    have hwK : w ∈ K := ⟨ball_subset_closedBall hwA.1,fun he => hwA.2 (ball_subset_closedBall he)⟩
    have hQw : AnalyticAt ℂ (fun u => Q (u,p)) w :=
      (hQ (w,p) ⟨hwK,hp⟩).comp (f := fun u : ℂ => (u,p)) (analyticAt_id.prod analyticAt_const)
    have hQn := hne p hp w hwK
    have hQsq : (fun u => Q (u,p)^2) =ᶠ[𝓝 w] quadraticRootPolynomial (τ p) (s p) := by
      filter_upwards [(isOpen_ball.sdiff isClosed_closedBall).mem_nhds hwA] with u hu
      exact hsq p hp u ⟨ball_subset_closedBall hu.1,fun he => hu.2 (ball_subset_closedBall he)⟩
    have hQd := hasDerivAt_root_of_sq_eq_quadratic (fun u => Q (u,p)) (τ p) (s p) w hQw hQn hQsq
    have hFd : HasDerivAt (fun u => F (u,p)) ((Q (w,p))⁻¹ • g (w,p)) w :=
      hasDerivAt_nativeAnnularPrimitiveAtAnchor D c r R hr (hrρ.trans hρR) V hV hD
        (c+ρ) p hp (hperiod p hp) w hwA
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2
    intro L
    have hLfd : HasDerivAt (fun u => L (F (u,p))/Q (u,p))
        (((L ((Q (w,p))⁻¹ • g (w,p)))*Q (w,p) -
          L (F (w,p))*((w-τ p)/Q (w,p)))/(Q (w,p))^2) w :=
      (L.hasFDerivAt.comp_hasDerivAt w hFd).fun_div hQd hQn
    have hlf : HasDerivAt (fun u => L (f (u,p)))
        ((L ((Q (w,p))⁻¹ • g (w,p))*Q (w,p) -
          L (F (w,p))*((w-τ p)/Q (w,p)))/(Q (w,p))^2) w := by
      simpa only [f, map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm] using hLfd
    have hnf : HasDerivAt (fun u => L (f (u,p)))
        (L (deriv (fun u => f (u,p)) w)) w :=
      L.hasFDerivAt.comp_hasDerivAt w
        ((hf (w,p) ⟨hwA,hp⟩).comp (f := fun u : ℂ => (u,p))
          (analyticAt_id.prod analyticAt_const)).differentiableAt.hasDerivAt
    rw [map_add, map_smul, map_smul, ← hnf.deriv, hlf.deriv, ← hsq p hp w hwK]
    simp only [f, map_smul, smul_eq_mul]
    field_simp
    ring
  · intro p hp z hz
    have hP (w : ℂ) (hw : w ∈ sphere c ρ) :
        HasDerivAt (fun u => nativeAnnularPrimitive D c r R (u,p)) (D (w,p)) w :=
      hasDerivAt_nativeAnnularPrimitive D c r R hr (hrρ.trans hρR) V hV hD p hp (hperiod p hp) w (hcircle hw)
    have h := norm_nativeCircleCauchyTransform_primitive_quotient_le
      (fun u => nativeAnnularPrimitive D c r R (u,p)) (fun u => D (u,p)) (fun u => Q (u,p))
      c ρ a δ M hρ.le haρ hδ hM hP (hbound p hp) (hQlower p hp) z hz
    simpa only [H, f, F, nativeAnnularPrimitiveAtAnchor, nativeCircleCauchyTransform] using h

end NLS.ComplexAnalysis
