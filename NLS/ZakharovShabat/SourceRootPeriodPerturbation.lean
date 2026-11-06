import NLS.ZakharovShabat.SourceLemma12_3
import NLS.ComplexAnalysis.RootPeriodComparison

/-! # Stability of the normalizing standard-root period

A complex analytic numerator close to one on the gap has a period close
to -i after division by 2π. This supplies a quantitative nonvanishing
criterion without any complex-valued mean-value assertion.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A uniform gap bound controls the original normalized root period. -/
theorem SourceCriticalRootPeriodCircle.norm_normalized_period_le_of_gap_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {k : ℤ}
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ k) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (P.center:ℂ) P.radius))
    (e : ℝ) (hgap : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖f z‖ ≤ e) :
    ‖(2*(Real.pi:ℂ))⁻¹*(∮ z in C((P.center:ℂ),P.radius),
      f z/sourceStandardRoot hp hp1 ψ k z)‖ ≤ e := by
  obtain ⟨z,hz,_,hb,_⟩ := P.lemma12_3_circle f hf
  rw [PiecewiseC1Loop.integral_circle] at hb
  exact hb.trans (hgap z hz)

/-- A gap bound on f-1 controls the normalized original-circle period. -/
theorem SourceCriticalRootPeriodCircle.norm_normalized_period_add_I_le
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {k : ℤ}
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ k) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (P.center:ℂ) P.radius))
    (ε : ℝ) (hgap : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖f z-1‖ ≤ ε) :
    ‖(2*(Real.pi:ℂ))⁻¹*(∮ z in C((P.center:ℂ),P.radius),
      f z/sourceStandardRoot hp hp1 ψ k z)+I‖ ≤ ε := by
  have hdiff : AnalyticOnNhd ℂ (fun z => f z-1) (closedBall (P.center:ℂ) P.radius) :=
    hf.sub analyticOnNhd_const
  obtain ⟨z,hz,_,hb,_⟩ := P.lemma12_3_circle (fun z => f z-1) hdiff
  rw [PiecewiseC1Loop.integral_circle] at hb
  have hw : ContinuousOn (sourceStandardRoot hp hp1 ψ k) (sphere (P.center:ℂ) P.radius) :=
    (sourceStandardRoot_analyticOnNhd hp hp1 ψ k).continuousOn.mono (fun z hz =>
      P.sphere_subset_rootDomain hz k)
  have hw0 : ∀ z ∈ sphere (P.center:ℂ) P.radius, sourceStandardRoot hp hp1 ψ k z ≠ 0 :=
    fun z hz => sourceStandardRoot_ne_zero_off_segment hp hp1 ψ k z (P.sphere_subset_rootDomain hz k)
  have hfi : CircleIntegrable (fun z => f z/sourceStandardRoot hp hp1 ψ k z) (P.center:ℂ) P.radius :=
    ((hf.continuousOn.mono sphere_subset_closedBall).div hw hw0).circleIntegrable P.radius_pos.le
  have hci : CircleIntegrable (fun z => (1:ℂ)/sourceStandardRoot hp hp1 ψ k z) (P.center:ℂ) P.radius :=
    (continuousOn_const.div hw hw0).circleIntegrable P.radius_pos.le
  have hconst := P.standardRoot_local_circle_period (fun _ => (1:ℂ)) analyticOnNhd_const
  simp only [intervalIntegral.integral_const,sub_zero,one_smul,mul_one] at hconst
  have he : (∮ z in C((P.center:ℂ),P.radius), (f z-1)/sourceStandardRoot hp hp1 ψ k z) =
      (∮ z in C((P.center:ℂ),P.radius), f z/sourceStandardRoot hp hp1 ψ k z)-
      (∮ z in C((P.center:ℂ),P.radius), (1:ℂ)/sourceStandardRoot hp hp1 ψ k z) := by
    simp only [sub_div]
    exact circleIntegral.integral_sub hfi hci
  rw [he,hconst] at hb
  have hπ : (2*(Real.pi:ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have he' : (2*(Real.pi:ℂ))⁻¹ *
      ((∮ z in C((P.center:ℂ),P.radius), f z/sourceStandardRoot hp hp1 ψ k z)-
        (-(2*(Real.pi:ℂ))*I)) =
      (2*(Real.pi:ℂ))⁻¹*(∮ z in C((P.center:ℂ),P.radius), f z/sourceStandardRoot hp hp1 ψ k z)+I := by
    field_simp [hπ]
    ring
  rw [he'] at hb
  exact hb.trans (hgap z hz)

/-- The normalized period is bounded away from zero whenever the gap error is below one. -/
theorem SourceCriticalRootPeriodCircle.normalized_period_lower_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {k : ℤ}
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ k) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (P.center:ℂ) P.radius))
    (ε : ℝ) (hgap : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖f z-1‖ ≤ ε) :
    1-ε ≤ ‖(2*(Real.pi:ℂ))⁻¹*(∮ z in C((P.center:ℂ),P.radius),
      f z/sourceStandardRoot hp hp1 ψ k z)‖ := by
  have hb := P.norm_normalized_period_add_I_le f hf ε hgap
  have ht := norm_sub_le ((2*(Real.pi:ℂ))⁻¹*(∮ z in C((P.center:ℂ),P.radius),
    f z/sourceStandardRoot hp hp1 ψ k z)+I)
    ((2*(Real.pi:ℂ))⁻¹*(∮ z in C((P.center:ℂ),P.radius), f z/sourceStandardRoot hp hp1 ψ k z))
  simp only [add_sub_cancel_left,norm_I] at ht
  linarith

/-- Strict gap smallness makes the actual original-circle period nonzero. -/
theorem SourceCriticalRootPeriodCircle.period_ne_zero_of_gap_error_lt_one
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {k : ℤ}
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ k) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (P.center:ℂ) P.radius))
    (ε : ℝ) (hε : ε < 1)
    (hgap : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖f z-1‖ ≤ ε) :
    (∮ z in C((P.center:ℂ),P.radius), f z/sourceStandardRoot hp hp1 ψ k z) ≠ 0 := by
  intro he
  have hb := P.normalized_period_lower_bound f hf ε hgap
  rw [he,mul_zero,norm_zero] at hb
  linarith

/-- The cancellation equation and three gap bounds give the quantitative root estimate.
The normalizing error is complex-valued and only its norm is used. -/
theorem SourceCriticalRootPeriodCircle.root_difference_le_of_gap_bounds
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {k : ℤ}
    (P : SourceCriticalRootPeriodCircle hp hp1 ψ k)
    (sigma rho : ℂ) (f E Q : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall (P.center:ℂ) P.radius))
    (hE : AnalyticOnNhd ℂ E (closedBall (P.center:ℂ) P.radius))
    (hQ : AnalyticOnNhd ℂ Q (closedBall (P.center:ℂ) P.radius))
    (ε e q : ℝ) (hε : ε < 1)
    (hgapf : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖f z-1‖ ≤ ε)
    (hgapE : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖E z‖ ≤ e)
    (hgapQ : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖Q z‖ ≤ q)
    (hid : (sigma-rho)*(∮ z in C((P.center:ℂ),P.radius), f z/sourceStandardRoot hp hp1 ψ k z) =
      (∮ z in C((P.center:ℂ),P.radius), E z/sourceStandardRoot hp hp1 ψ k z)+
      (∮ z in C((P.center:ℂ),P.radius), Q z/sourceStandardRoot hp hp1 ψ k z)) :
    ‖sigma-rho‖ ≤ (e+q)/(1-ε) := by
  let J (g : ℂ → ℂ) := (2*(Real.pi:ℂ))⁻¹*(∮ z in C((P.center:ℂ),P.radius),
    g z/sourceStandardRoot hp hp1 ψ k z)
  have hi : (sigma-rho)*J f = J E+J Q := by
    dsimp only [J]
    rw [mul_left_comm,hid,mul_add]
  exact norm_root_difference_le_of_period_identity sigma rho (J f) (J E) (J Q)
    (1-ε) e q (by linarith) (P.normalized_period_lower_bound f hf ε hgapf)
    (P.norm_normalized_period_le_of_gap_bound E hE e hgapE)
    (P.norm_normalized_period_le_of_gap_bound Q hQ q hgapQ) hi

end NLS.ZakharovShabat
