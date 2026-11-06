import NLS.ComplexAnalysis.ParametricEvenSquareDescent
import NLS.ComplexAnalysis.LocalAnalyticSquareRoot

/-! # Local even analytic families depend analytically on a squared input -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem analyticAt_evenFamily_of_analytic_square
    (F : ℂ × A → ℂ) (d : A → ℂ) (a : A)
    (hF : AnalyticAt ℂ F (d a,a)) (heven : ∀ b e, F (-e,b) = F (e,b))
    (hsq : AnalyticAt ℂ (fun b => (d b)^2) a) :
    AnalyticAt ℂ (fun b => F (d b,b)) a := by
  by_cases hzero : d a = 0
  · have hF0 : AnalyticAt ℂ F (0,a) := by simpa only [hzero] using hF
    obtain ⟨e,he,hball⟩ := Metric.mem_nhds_iff.mp hF0.eventually_analyticAt
    let R : ℝ := e/2
    have hR : 0 < R := half_pos he
    let q : A → ℂ := fun b => (d b)^2
    let O : Set A := {b | AnalyticAt ℂ q b}
    have hO : IsOpen O := isOpen_analyticAt ℂ q
    have hq : AnalyticOnNhd ℂ q O := fun _ hb => hb
    let V : Set A := ball a R ∩ (O ∩ q ⁻¹' ball 0 (R^2))
    have hV : IsOpen V := isOpen_ball.inter (hq.continuousOn.isOpen_inter_preimage hO isOpen_ball)
    have haV : a ∈ V := by
      refine ⟨mem_ball_self hR,hsq,?_⟩
      change (d a)^2 ∈ ball (0 : ℂ) (R^2)
      rw [hzero,zero_pow (by decide : 2 ≠ 0)]
      exact mem_ball_self (sq_pos_of_pos hR)
    have hFV : AnalyticOnNhd ℂ F (closedBall 0 R ×ˢ V) := by
      intro x hx
      apply hball
      rw [mem_ball,Prod.dist_eq]
      apply max_lt
      · have hh := mem_closedBall.mp hx.1
        exact hh.trans_lt (half_lt_self he)
      · exact (mem_ball.mp hx.2.1).trans (half_lt_self he)
    have hd : ∀ b ∈ V, ‖d b‖ < R := by
      intro b hb
      have hh : ‖d b‖^2 < R^2 := by simpa only [mem_preimage,q,mem_ball,dist_zero_right,norm_pow] using hb.2.2
      exact (sq_lt_sq₀ (norm_nonneg _) hR.le).mp hh
    exact analyticOnNhd_evenFamily_of_analytic_square F R hR V hV hFV
      (fun b _ e _ => heven b e) d hd (fun b hb => hb.2.1) a haV
  · obtain ⟨V,hV,haV,s,hs,hsa,hsquare⟩ := exists_local_analytic_squareRoot
      (fun b => (d b)^2) a (d a) hsq hzero rfl
    have hFs : AnalyticAt ℂ F (s a,a) := by rwa [hsa]
    have hc := hFs.comp (f := fun b => (s b,b)) ((hs a haV).prod analyticAt_id)
    apply hc.congr
    filter_upwards [hV.mem_nhds haV] with b hb
    dsimp only [Function.comp_def]
    have heq : (s b)^2 = (d b)^2 := (hsquare b hb).2
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp heq with h | h
    · rw [h]
    · rw [h,heven]

end NLS.ComplexAnalysis
