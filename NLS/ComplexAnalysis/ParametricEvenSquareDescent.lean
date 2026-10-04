import NLS.ComplexAnalysis.ParametricCircleTransforms

/-! # Analytic descent of even families through squaring

A fixed Cauchy circle replaces an even function of a square root by an
analytic function of its square. The construction is jointly analytic in
Banach parameters and remains valid at the double root zero.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- A Cauchy kernel depending on the squared coordinate alone. -/
def parametricEvenSquareDescent (F : ℂ × A → ℂ) (R : ℝ) (x : ℂ × A) : ℂ :=
  (2*Real.pi*I:ℂ)⁻¹ * ∮ w in C(0,R), w*F (w,x.2)/(w^2-x.1)

/-- The square-coordinate transform is jointly analytic inside the
squared radius, without selecting a branch of the square root. -/
theorem analyticOnNhd_parametricEvenSquareDescent
    (F : ℂ × A → ℂ) (R : ℝ) (hR : 0 ≤ R) (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (sphere 0 R ×ˢ V)) :
    AnalyticOnNhd ℂ (parametricEvenSquareDescent F R) (ball 0 (R^2) ×ˢ V) := by
  let T : ℂ × (ℂ × A) → ℂ × A := fun t => (t.1,t.2.2)
  let K : ℂ × (ℂ × A) → ℂ := fun t => t.1^2-t.2.1
  let D : Set (ℂ × (ℂ × A)) := {t | AnalyticAt ℂ F (T t) ∧ K t ≠ 0}
  let G : ℂ × (ℂ × A) → ℂ := fun t => t.1*F (T t)/K t
  have hT : Continuous T := by dsimp [T]; fun_prop
  have hK : Continuous K := by dsimp [K]; fun_prop
  have hD : IsOpen D := ((isOpen_analyticAt ℂ F).preimage hT).inter
    (isOpen_ne_fun hK continuous_const)
  have hG : AnalyticOnNhd ℂ G D := by
    intro t ht
    have ha : AnalyticAt ℂ (fun t : ℂ × (ℂ × A) => t.2.2) t := analyticAt_snd.comp (f := fun t : ℂ × (ℂ × A) => t.2) analyticAt_snd
    have hq : AnalyticAt ℂ (fun t : ℂ × (ℂ × A) => t.2.1) t := analyticAt_fst.comp (f := fun t : ℂ × (ℂ × A) => t.2) analyticAt_snd
    exact (analyticAt_fst.mul (ht.1.comp (f := T) (analyticAt_fst.prod ha))).div
      ((analyticAt_fst.pow 2).sub hq) ht.2
  have hcircle : ∀ x ∈ ball (0:ℂ) (R^2) ×ˢ V, ∀ w ∈ sphere (0:ℂ) R, (w,x) ∈ D := by
    intro x hx w hw
    refine ⟨hF (w,x.2) ⟨hw,hx.2⟩,?_⟩
    have hwn : ‖w‖ = R := by simpa only [mem_sphere,dist_zero_right] using hw
    have hxn : ‖x.1‖ < R^2 := by simpa only [mem_ball,dist_zero_right] using hx.1
    intro he
    have heq : w^2 = x.1 := sub_eq_zero.mp he
    have hn := congrArg norm heq
    rw [norm_pow,hwn] at hn
    linarith
  have hraw := analyticOnNhd_circleIntegral_of_jointAnalytic G hD hG 0 R hR
    (isOpen_ball.prod hV) hcircle
  intro x hx
  exact analyticAt_const.mul (hraw x hx)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- At a squared argument the transform is the average of the values
at the two roots, including when both roots are zero. -/
theorem parametricEvenSquareDescent_sq
    (F : ℂ × A → ℂ) (R : ℝ) (hR : 0 < R) (a : A)
    (hF : AnalyticOnNhd ℂ (fun w => F (w,a)) (closedBall 0 R))
    (d : ℂ) (hd : ‖d‖ < R) :
    parametricEvenSquareDescent F R (d^2,a) = (F (d,a)+F (-d,a))/2 := by
  have hc (z : ℂ) (hz : ‖z‖ < R) :
      (2*Real.pi*I:ℂ)⁻¹ * (∮ w in C(0,R), F (w,a)/(w-z)) = F (z,a) := by
    have hf : DiffContOnCl ℂ (fun w => F (w,a)) (ball 0 R) :=
      DiffContOnCl.mk_ball (hF.differentiableOn.mono ball_subset_closedBall) hF.continuousOn
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
      hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (by simpa only [mem_ball,dist_zero_right] using hz)
  have hint (z : ℂ) (hz : ‖z‖ < R) : CircleIntegrable (fun w => F (w,a)/(w-z)) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    have hden : ContinuousOn (fun w : ℂ => w-z) (sphere 0 R) :=
      continuousOn_id.sub continuousOn_const
    exact (hF.continuousOn.mono sphere_subset_closedBall).div hden (fun w hw => by
        have hwn : ‖w‖ = R := by simpa only [mem_sphere,dist_zero_right] using hw
        intro he
        have heq := sub_eq_zero.mp he
        rw [heq] at hwn
        linarith)
  have hneg : ‖-d‖ < R := by simpa only [norm_neg] using hd
  have hpoint (w : ℂ) (hw : w ∈ sphere (0:ℂ) R) :
      w*F (w,a)/(w^2-d^2) = (1/2:ℂ)*(F (w,a)/(w-d)+F (w,a)/(w-(-d))) := by
    have hwn : ‖w‖ = R := by simpa only [mem_sphere,dist_zero_right] using hw
    have hwd : w-d ≠ 0 := by intro h; have := sub_eq_zero.mp h; subst w; linarith
    have hwn : w-(-d) ≠ 0 := by intro h; have := sub_eq_zero.mp h; subst w; simp only [norm_neg] at hwn; exact (ne_of_lt hd) hwn
    have hwq : w^2-d^2 ≠ 0 := by
      rw [sq_sub_sq]
      exact mul_ne_zero (by simpa only [sub_neg_eq_add] using hwn) hwd
    field_simp
    ring
  unfold parametricEvenSquareDescent
  dsimp only
  rw [circleIntegral.integral_congr hR.le hpoint,circleIntegral.integral_const_mul,
    circleIntegral.integral_add (hint d hd) (hint (-d) hneg)]
  linear_combination (hc d hd)/2 + (hc (-d) hneg)/2

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- An even family is recovered exactly from its square-coordinate
transform, so the construction is a descent rather than an approximation. -/
theorem parametricEvenSquareDescent_sq_of_even
    (F : ℂ × A → ℂ) (R : ℝ) (hR : 0 < R) (a : A)
    (hF : AnalyticOnNhd ℂ (fun w => F (w,a)) (closedBall 0 R))
    (heven : ∀ d ∈ ball (0:ℂ) R, F (-d,a) = F (d,a))
    (d : ℂ) (hd : ‖d‖ < R) :
    parametricEvenSquareDescent F R (d^2,a) = F (d,a) := by
  rw [parametricEvenSquareDescent_sq F R hR a hF d hd,
    heven d (by simpa only [mem_ball,dist_zero_right] using hd)]
  ring

/-- An even analytic family may be evaluated at an arbitrary square-root
selection: analyticity of its square suffices, including at its zeros. -/
theorem analyticOnNhd_evenFamily_of_analytic_square
    (F : ℂ × A → ℂ) (R : ℝ) (hR : 0 < R) (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (closedBall 0 R ×ˢ V))
    (heven : ∀ a ∈ V, ∀ d ∈ ball (0:ℂ) R, F (-d,a) = F (d,a))
    (d : A → ℂ) (hd : ∀ a ∈ V, ‖d a‖ < R)
    (hsq : AnalyticOnNhd ℂ (fun a => (d a)^2) V) :
    AnalyticOnNhd ℂ (fun a => F (d a,a)) V := by
  have hdesc := analyticOnNhd_parametricEvenSquareDescent F R hR.le V hV
    (hF.mono (prod_mono sphere_subset_closedBall Subset.rfl))
  intro a ha
  have hmem : ((d a)^2,a) ∈ ball (0:ℂ) (R^2) ×ˢ V := by
    refine ⟨?_,ha⟩
    simp only [mem_ball,dist_zero_right,norm_pow]
    exact (sq_lt_sq₀ (norm_nonneg _) hR.le).mpr (hd a ha)
  have hcomp := (hdesc _ hmem).comp (f := fun a => ((d a)^2,a))
    ((hsq a ha).prod analyticAt_id)
  apply hcomp.congr
  filter_upwards [hV.mem_nhds ha] with b hb
  exact parametricEvenSquareDescent_sq_of_even F R hR b
    (fun z hz => (hF (z,b) ⟨hz,hb⟩).comp
      (f := fun z : ℂ => (z,b)) (analyticAt_id.prod analyticAt_const))
    (heven b hb) (d b) (hd b hb)

end NLS.ComplexAnalysis
