import NLS.ComplexAnalysis.PiecewiseLoopPullback
import NLS.ComplexAnalysis.PiecewiseContourPeriod

/-! # Actual loop transport under a quadratic energy change

The map is z squared minus the literal energy shift. The pullback keeps
its exact two-z Jacobian; winding counts both algebraic preimages.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

def quadraticEnergyMap (c z : ℂ) : ℂ := z^2-c

def quadraticEnergyLoop (Γ : PiecewiseC1Loop) (c : ℂ) : PiecewiseC1Loop :=
  Γ.map (quadraticEnergyMap c) (by unfold quadraticEnergyMap; fun_prop)

theorem integral_quadraticEnergyLoop
    (Γ : PiecewiseC1Loop) (c : ℂ) (f g : ℂ → ℂ) (U : Set ℂ) (hΓ : Γ.Inside U)
    (hpull : ∀ z ∈ U, f (z^2-c)*(2*z) = g z) :
    (quadraticEnergyLoop Γ c).integral f = Γ.integral g := by
  apply Γ.integral_map_of_holomorphic_pullback _ _ (fun z => 2*z) f g U hΓ _ hpull
  intro z _
  simpa [quadraticEnergyMap] using ((hasDerivAt_id z).pow 2).sub_const c

theorem windingIntegral_quadraticEnergyLoop
    (Γ : PiecewiseC1Loop) (c a : ℂ) (hΓ : Γ.Inside {z : ℂ | z ≠ a ∧ z ≠ -a}) :
    (quadraticEnergyLoop Γ c).windingIntegral (a^2-c) = Γ.windingIntegral a+Γ.windingIntegral (-a) := by
  let U : Set ℂ := {z | z ≠ a ∧ z ≠ -a}
  have hinv (b : ℂ) (hb : b = a ∨ b = -a) : ContinuousOn (fun z => (z-b)⁻¹) U := by
    intro z hz
    have hne : z-b ≠ 0 := by
      rcases hb with rfl | rfl
      · exact sub_ne_zero.mpr hz.1
      · exact sub_ne_zero.mpr hz.2
    exact ((continuousAt_id.sub continuousAt_const).inv₀ hne).continuousWithinAt
  have he : (quadraticEnergyLoop Γ c).integral (fun w => (w-(a^2-c))⁻¹) =
      Γ.integral (fun z => (z-a)⁻¹+(z-(-a))⁻¹) := by
    apply integral_quadraticEnergyLoop Γ c _ _ U hΓ
    intro z hz
    have hza := sub_ne_zero.mpr hz.1
    have hzna := sub_ne_zero.mpr hz.2
    have hq : z^2-a^2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero (by simpa only [sub_neg_eq_add] using hzna) hza
    have hh : z^2-c-(a^2-c) = z^2-a^2 := by ring
    rw [hh]
    field_simp
    ring
  change (2*Real.pi*I : ℂ)⁻¹*(quadraticEnergyLoop Γ c).integral (fun w => (w-(a^2-c))⁻¹) = _
  rw [he,Γ.integral_add _ _ (hinv a (Or.inl rfl)) (hinv (-a) (Or.inr rfl)) hΓ]
  change _ = (2*Real.pi*I : ℂ)⁻¹*Γ.integral (fun z => (z-a)⁻¹)+
    (2*Real.pi*I : ℂ)⁻¹*Γ.integral (fun z => (z-(-a))⁻¹)
  ring

theorem windingIntegral_circle_eq_zero_of_not_mem_closedBall
    (b a : ℂ) (R : ℝ) (hR : 0 ≤ R) (ha : a ∉ closedBall b R) :
    (PiecewiseC1Loop.circle b R).windingIntegral a = 0 := by
  have hf : AnalyticOnNhd ℂ (fun z => (z-a)⁻¹) (closedBall b R) := by
    intro z hz
    have hne : z-a ≠ 0 := sub_ne_zero.mpr (fun he => ha (he ▸ hz))
    exact (analyticAt_id.sub analyticAt_const).inv hne
  have he := (DiffContOnCl.mk_ball (hf.differentiableOn.mono ball_subset_closedBall) hf.continuousOn).circleIntegral_eq_zero hR
  change (2*Real.pi*I : ℂ)⁻¹*(PiecewiseC1Loop.circle b R).integral (fun z => (z-a)⁻¹) = 0
  rw [PiecewiseC1Loop.integral_circle,he,mul_zero]

theorem windingIntegral_quadraticEnergyCircle_one
    (b a c : ℂ) (R : ℝ) (ha : a ∈ ball b R) (hna : -a ∉ closedBall b R) :
    (quadraticEnergyLoop (PiecewiseC1Loop.circle b R) c).windingIntegral (a^2-c) = 1 := by
  have hR : 0 < R := dist_nonneg.trans_lt (mem_ball.mp ha)
  have hin : (PiecewiseC1Loop.circle b R).Inside {z : ℂ | z ≠ a ∧ z ≠ -a} := by
    intro i t
    have hz : (PiecewiseC1Loop.circle b R).edge i t ∈ sphere b R :=
      circleMap_mem_sphere b hR.le ((2*Real.pi)*(t : ℝ))
    refine ⟨?_,?_⟩
    · intro he
      exact (mem_ball.mp ha).ne (he ▸ mem_sphere.mp hz)
    · intro he
      exact hna (he ▸ sphere_subset_closedBall hz)
  rw [windingIntegral_quadraticEnergyLoop _ c a hin,PiecewiseC1Loop.windingIntegral_circle b a R ha,
    windingIntegral_circle_eq_zero_of_not_mem_closedBall b (-a) R hR.le hna,add_zero]

end NLS.ComplexAnalysis
