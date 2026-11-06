import NLS.ComplexAnalysis.AnalyticCollapsedQuadraticSolution
import NLS.ComplexAnalysis.BoundedParametricQuadraticSolution

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- A common analytic disc and squared-gap domain suffice for joint
analyticity of the actual centered mean-free numerator. -/
theorem analyticOnNhd_centeredMeanFree_of_disc
    (f : ℂ × A → ℂ) (s : A → ℂ) (U : Set A) (hU : IsOpen U) (R : ℝ)
    (hf : AnalyticOnNhd ℂ f (closedBall (0:ℂ) R ×ˢ U))
    (hs : AnalyticOnNhd ℂ s U) (hsmall : ∀ p∈U, ‖sqrt (s p)‖<R) :
    AnalyticOnNhd ℂ (centeredMeanFree f s) (closedBall (0:ℂ) R ×ˢ U) := by
  have hm (p : A) (hp : p∈U) :
      AnalyticAt ℂ (fun p => parametricCosineMean f (fun _ => 0) (sqrt (s p),p)) p := by
    apply analyticAt_parametricCosineMean_of_squared_gap_segment f (fun _ => 0) (fun p => sqrt (s p))
      (ball (0:ℂ) R ×ˢ U) (isOpen_ball.prod hU)
      (hf.mono (prod_mono ball_subset_closedBall Subset.rfl)) p analyticAt_const
      (by simpa only [complex_sqrt_sq] using hs p hp)
    intro θ _
    refine ⟨?_,hp⟩
    rw [zero_add,mem_ball,dist_zero_right,norm_mul]
    have hc : ‖(Real.cos θ : ℂ)‖≤1 := by simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    exact (mul_le_mul_of_nonneg_left hc (norm_nonneg _)).trans_lt (by simpa only [mul_one] using hsmall p hp)
  intro t ht
  exact (hf t ht).sub (((hm t.2 ht.2).comp (f := fun t : ℂ × A => t.2) analyticAt_snd).div_const)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- Subtracting the original cosine mean costs at most a factor two in
any common disc bound. -/
theorem norm_centeredMeanFree_le_of_disc_bound
    (f : ℂ × A → ℂ) (s : A → ℂ) (U : Set A) (R B : ℝ)
    (hsmall : ∀ p∈U, ‖sqrt (s p)‖≤R)
    (hb : ∀ p∈U, ∀ z∈closedBall (0:ℂ) R, ‖f (z,p)‖≤B)
    (p : A) (hp : p∈U) (z : ℂ) (hz : z∈closedBall (0:ℂ) R) :
    ‖centeredMeanFree f s (z,p)‖≤2*B := by
  have hcurve (θ : ℝ) : sqrt (s p)*(Real.cos θ : ℂ)∈closedBall (0:ℂ) R := by
    rw [mem_closedBall,dist_zero_right,norm_mul]
    have hc : ‖(Real.cos θ : ℂ)‖≤1 := by simpa only [norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one θ
    exact (mul_le_mul_of_nonneg_left hc (norm_nonneg _)).trans (by simpa only [mul_one] using hsmall p hp)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := Real.pi) (fun θ _ => hb p hp _ (hcurve θ))
  have hm : ‖parametricCosineMean f (fun _ => 0) (sqrt (s p),p)/(Real.pi : ℂ)‖≤B := by
    rw [parametricCosineMean,norm_div,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    apply (div_le_iff₀ Real.pi_pos).mpr
    simpa only [zero_add,sub_zero,abs_of_pos Real.pi_pos] using hi
  exact (norm_sub_le _ _).trans (by linarith [hb p hp z hz])

/-- A quantitative centered mean-free primitive on one fixed source
and energy domain, including nonzero and collapsed squared gaps. -/
theorem exists_bounded_analytic_centered_mean_free_quadratic_solution
    (f : ℂ × A → ℂ) (s : A → ℂ) (U : Set A) (hU : IsOpen U)
    (R B : ℝ) (hR : 0<R) (hB : 0≤B)
    (hf : AnalyticOnNhd ℂ f (closedBall (0:ℂ) R ×ˢ U))
    (hs : AnalyticOnNhd ℂ s U) (hsmall : ∀ p∈U, ‖s p‖<(R/8)^2)
    (hb : ∀ p∈U, ∀ z∈closedBall (0:ℂ) R, ‖f (z,p)‖≤B) :
    ∃ H : ℂ × A → ℂ, AnalyticOnNhd ℂ H (ball (0:ℂ) (R/2) ×ˢ U) ∧
      (∀ p∈U, ∀ z∈ball (0:ℂ) (R/2),
        (z^2-s p)*deriv (fun w => H (w,p)) z+z*H (z,p)=centeredMeanFree f s (z,p)) ∧
      ∀ p∈U, ∀ z∈closedBall (0:ℂ) (R/4), ‖H (z,p)‖≤32*Real.pi*B/R := by
  have hroot (p : A) (hp : p∈U) : ‖sqrt (s p)‖<R/8 := by
    have hh : ‖sqrt (s p)‖^2=‖s p‖ := by rw [← norm_pow,complex_sqrt_sq]
    nlinarith [hsmall p hp,norm_nonneg (sqrt (s p))]
  have hsmall' (p : A) (hp : p∈U) : ‖s p‖<(R/4)^2 := by nlinarith [hsmall p hp]
  have hg := analyticOnNhd_centeredMeanFree_of_disc f s U hU R hf hs
    (fun p hp => (hroot p hp).trans (by linarith))
  have hgb (p : A) (hp : p∈U) (z : ℂ) (hz : z∈closedBall (0:ℂ) R) :
      ‖centeredMeanFree f s (z,p)‖≤2*B := norm_centeredMeanFree_le_of_disc_bound f s U R B
        (fun p hp => (hroot p hp).le.trans (by linarith)) hb p hp z hz
  have hQ := analyticOnNhd_centeredQuadraticRoot s (R/4) R (by positivity) U hs hsmall'
  have hQn (p : A) (hp : p∈U) (z : ℂ) (hz : z∈closedBall (0:ℂ) R \ ball 0 (R/4)) :
      centeredQuadraticRoot s (z,p)≠0 := centeredQuadraticRoot_ne_zero s z p (R/4) (by positivity)
        (by simpa only [mem_ball,dist_zero_right,not_lt] using hz.2) (hsmall' p hp)
  have hQsq (p : A) (hp : p∈U) (z : ℂ) (hz : z∈closedBall (0:ℂ) R \ ball 0 (R/4)) :
      centeredQuadraticRoot s (z,p)^2=quadraticRootPolynomial 0 (s p) z := by
    have hzn : z≠0 := by
      have hh : R/4≤‖z‖ := by simpa only [mem_ball,dist_zero_right,not_lt] using hz.2
      exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0<R/4) hh)
    simpa only [quadraticRootPolynomial,sub_zero] using centeredQuadraticRoot_sq s z p hzn
  have hQlower (p : A) (hp : p∈U) (z : ℂ) (hz : z∈sphere (0:ℂ) (R/2)) :
      R/4≤‖centeredQuadraticRoot s (z,p)‖ := by
    have hd : ‖z‖=R/2 := by simpa only [mem_sphere,dist_zero_right] using hz
    have hzn : z≠0 := norm_pos_iff.mp (hd.symm ▸ (by positivity : 0<R/2))
    have hsq := congrArg norm (centeredQuadraticRoot_sq s z p hzn)
    rw [norm_pow] at hsq
    have hh := norm_sub_norm_le (z^2) (s p)
    rw [norm_pow,hd] at hh
    nlinarith [hsmall p hp,norm_nonneg (centeredQuadraticRoot s (z,p))]
  have hperiod (p : A) (hp : p∈U) :
      (∮ z in C((0:ℂ),R/4), centeredMeanFree f s (z,p)/centeredQuadraticRoot s (z,p))=0 := by
    apply circleIntegral_centeredMeanFree_div_root_eq_zero f s p (R/4) R
      ((hroot p hp).trans (by linarith)) (by linarith)
    intro z hz
    exact (hf (z,p) ⟨hz,hp⟩).comp (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
  have hbound (p : A) (hp : p∈U) (z : ℂ) (hz : z∈sphere (0:ℂ) (R/2)) :
      ‖centeredMeanFree f s (z,p)/centeredQuadraticRoot s (z,p)‖≤8*B/R := by
    have hz' : z∈closedBall (0:ℂ) R := closedBall_subset_closedBall (by linarith : R/2≤R) (sphere_subset_closedBall hz)
    rw [norm_div]
    apply (div_le_div₀ (by positivity : 0≤2*B) (hgb p hp z hz') (by positivity : 0<R/4) (hQlower p hp z hz)).trans_eq
    field_simp
    ring
  obtain ⟨H,hH,hODE,hHb⟩ := exists_bounded_analytic_parametric_quadratic_solution_of_zero_period
    (centeredMeanFree f s) (centeredQuadraticRoot s) (fun _ => 0) s 0 (R/4) (R/2) R (R/4) (R/4) (8*B/R)
    (by linarith) (by positivity) (by positivity) (by positivity) (by linarith) (by linarith)
    U hU hg hQ hQn hQsq hperiod hQlower hbound
  refine ⟨H,hH,?_,?_⟩
  · intro p hp z hz
    simpa only [quadraticRootPolynomial,sub_zero] using hODE p hp z hz
  · intro p hp z hz
    apply (hHb p hp z hz).trans_eq
    field_simp
    ring

end NLS.ComplexAnalysis
