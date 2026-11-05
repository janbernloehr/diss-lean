import NLS.ComplexAnalysis.CenteredMeanFreePeriod
import NLS.ComplexAnalysis.ParametricQuadraticSolution

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem exists_analytic_centered_mean_free_quadratic_solution
    (f : ℂ × A → ℂ) (s : A → ℂ) (a : A)
    (hf : AnalyticAt ℂ f (0,a)) (hs : AnalyticAt ℂ s a) (hs0 : s a = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ V : Set A, IsOpen V ∧ a ∈ V ∧ ∃ H : ℂ × A → ℂ,
      AnalyticOnNhd ℂ H (ball (0:ℂ) ρ ×ˢ V) ∧
      ∀ p ∈ V, ‖sqrt (s p)‖ < ρ ∧ ∀ z ∈ ball (0:ℂ) ρ,
        quadraticRootPolynomial 0 (s p) z*deriv (fun w => H (w,p)) z+z*H (z,p) =
          centeredMeanFree f s (z,p) := by
  let g := centeredMeanFree f s
  have hg : AnalyticAt ℂ g (0,a) := analyticAt_centeredMeanFree_of_collapse f s a hf hs hs0
  let D : Set (ℂ × A) := {t | AnalyticAt ℂ f t} ∩ ({t | AnalyticAt ℂ g t} ∩ {t | AnalyticAt ℂ s t.2})
  have hD : IsOpen D := (isOpen_analyticAt ℂ f).inter
    ((isOpen_analyticAt ℂ g).inter ((isOpen_analyticAt ℂ s).preimage continuous_snd))
  obtain ⟨W,U,hW,hU,h0W,haU,hWU⟩ := isOpen_prod_iff.mp hD 0 a ⟨hf,hg,hs⟩
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0W)
  let R := ε/2
  let ρ := ε/4
  let r := ε/8
  have hr : 0 < r := by dsimp [r];positivity
  have hrρ : r < ρ := by dsimp [r,ρ];linarith
  have hρR : ρ < R := by dsimp [ρ,R];linarith
  have hRε : R < ε := by dsimp [R];linarith
  have hsmallBall : closedBall (0:ℂ) R ⊆ W := fun z hz => hball (closedBall_subset_ball hRε hz)
  have hsU : AnalyticOnNhd ℂ s U := by
    intro p hp
    have hd : ((0:ℂ),p) ∈ D := hWU ⟨h0W,hp⟩
    exact hd.2.2
  let V : Set A := U ∩ {p | ‖s p‖ < r^2}
  have hV : IsOpen V := hsU.continuousOn.norm.isOpen_inter_preimage hU isOpen_Iio
  have haV : a ∈ V := ⟨haU,by change ‖s a‖ < r^2;rw [hs0,norm_zero];exact sq_pos_of_pos hr⟩
  have hsmall : ∀ p ∈ V, ‖s p‖ < r^2 := fun _ hp => hp.2
  have hfV : AnalyticOnNhd ℂ f (closedBall (0:ℂ) R ×ˢ V) := by
    intro t ht
    have hd : t ∈ D := hWU ⟨hsmallBall ht.1,ht.2.1⟩
    exact hd.1
  have hgV : AnalyticOnNhd ℂ g (closedBall (0:ℂ) R ×ˢ V) := by
    intro t ht
    have hd : t ∈ D := hWU ⟨hsmallBall ht.1,ht.2.1⟩
    exact hd.2.1
  have hQ := analyticOnNhd_centeredQuadraticRoot s r R hr V (hsU.mono inter_subset_left) hsmall
  have hQn (p : A) (hp : p ∈ V) (z : ℂ) (hz : z ∈ closedBall (0:ℂ) R \ ball 0 r) :
      centeredQuadraticRoot s (z,p) ≠ 0 :=
    centeredQuadraticRoot_ne_zero s z p r hr
      (by simpa only [mem_ball,dist_zero_right,not_lt] using hz.2) (hsmall p hp)
  have hQsq (p : A) (hp : p ∈ V) (z : ℂ) (hz : z ∈ closedBall (0:ℂ) R \ ball 0 r) :
      centeredQuadraticRoot s (z,p)^2 = quadraticRootPolynomial 0 (s p) z := by
    have hzn : z ≠ 0 := by
      have hzr : r ≤ ‖z‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hz.2
      exact norm_pos_iff.mp (hr.trans_le hzr)
    simpa only [quadraticRootPolynomial,sub_zero] using centeredQuadraticRoot_sq s z p hzn
  have hrootBound (p : A) (hp : p ∈ V) : ‖sqrt (s p)‖ < r := by
    have he : ‖sqrt (s p)‖^2 = ‖s p‖ := by rw [← norm_pow,complex_sqrt_sq]
    nlinarith [hsmall p hp,norm_nonneg (sqrt (s p))]
  have hperiod (p : A) (hp : p ∈ V) :
      (∮ z in C((0:ℂ),r), g (z,p)/centeredQuadraticRoot s (z,p)) = 0 := by
    apply circleIntegral_centeredMeanFree_div_root_eq_zero f s p r R (hrootBound p hp) (hrρ.trans hρR)
    intro z hz
    exact (hfV (z,p) ⟨hz,hp⟩).comp (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
  obtain ⟨H,hH,heq⟩ := exists_analytic_parametric_quadratic_solution_of_zero_period g (centeredQuadraticRoot s)
    (fun _ => 0) s 0 r ρ R hr hrρ hρR V hV hgV hQ hQn hQsq hperiod
  refine ⟨ρ,hr.trans hrρ,V,hV,haV,H,hH,?_⟩
  intro p hp
  exact ⟨(hrootBound p hp).trans hrρ,fun z hz => by simpa only [sub_zero] using heq p hp z hz⟩

end NLS.ComplexAnalysis
