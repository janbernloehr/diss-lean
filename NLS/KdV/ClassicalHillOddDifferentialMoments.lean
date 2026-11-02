import NLS.KdV.ClassicalHillWholeGapQuotients
import NLS.KdV.ClassicalHillAnnulusCoverage

/-! # Actual odd differential moments on the complete high contour tail

The root quotient and primitive square extend through the whole gap.
Cauchy cancellation applies to any entire energy numerator, including
the actual normalized numerator and a collapsed diagonal gap.
-/
noncomputable section
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem classicalHill_frequency_differential_radius_independence
    (P : ℂ → ℂ) (hP : AnalyticOnNhd ℂ P univ) (k : ℕ+) (m : ℕ) (q : Curve ℂ)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4)
    (hcover : ∀ z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
      r ≤ ‖z-(Real.pi : ℂ)*(k : ℕ)‖ → (z^2,q) ∈ classicalHillContinuationDomain) :
    (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*
        (P (z^2)/classicalHillContinuedRoot (z^2,q))*(2*z)) =
    ∮ z in C((Real.pi : ℂ)*(k : ℕ),r),
      (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*
        (P (z^2)/classicalHillContinuedRoot (z^2,q))*(2*z) := by
  let c : ℂ := (Real.pi : ℂ)*(k : ℕ)
  let f (z : ℂ) : ℂ := (classicalHillContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*
    (P (z^2)/classicalHillContinuedRoot (z^2,q))*(2*z)
  have hf : AnalyticOnNhd ℂ f (closedBall c (Real.pi/4) \ ball c r) := by
    intro z hz
    have ht := hcover z hz.1 (by simpa only [mem_ball,dist_eq_norm,not_lt] using hz.2)
    have hF := (analyticOnNhd_classicalHillContinuedPrimitive (z^2,q) ht).comp
      (f := fun z : ℂ => (z^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)
    have hR := (analyticOnNhd_classicalHillContinuedRoot (z^2,q) ht).comp
      (f := fun z : ℂ => (z^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)
    have hp := (hP (z^2) (mem_univ _)).comp (f := fun z : ℂ => z^2) (analyticAt_id.pow 2)
    exact ((hF.add analyticAt_const).pow m).mul (hp.div hR (classicalHillContinuedRoot_ne_zero _ ht))
      |>.mul (analyticAt_const.mul analyticAt_id)
  exact circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrpi countable_empty hf.continuousOn
    (fun z hz => (hf z ⟨ball_subset_closedBall hz.1.1,fun hh => hz.1.2 (ball_subset_closedBall hh)⟩).differentiableAt)

/-- A common complex source neighborhood supports cancellation of every
odd moment, before all high contour indices and all entire numerators. -/
theorem exists_classicalHill_high_odd_differential_moments (q : Curve ℂ) :
    ∃ M : ℕ, ∃ U : Set (Curve ℂ), 0 < M ∧ IsOpen U ∧ q ∈ U ∧
      ∀ a ∈ U, ∀ k : ℕ+, M ≤ (k : ℕ) → ∀ P : ℂ → ℂ, AnalyticOnNhd ℂ P univ →
        ∀ l : ℕ, (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
          (classicalHillContinuedPrimitive (z^2,a)+I*(k : ℂ)*Real.pi)^(2*l+1)*
            (P (z^2)/classicalHillContinuedRoot (z^2,a))*(2*z)) = 0 := by
  obtain ⟨r,N,V,hr,hrpi,hN,hV,hq,hfamily⟩ := exists_classicalHill_whole_gap_quotients q
  have hrho : 0 < r/8 := by positivity
  have hrhopi : r/8 ≤ Real.pi/4 := by linarith
  obtain ⟨Na,Va,_,hVa,hqa,hannulus⟩ := exists_classicalHill_high_annulus_neighborhood q (r/8) hrho hrhopi
  refine ⟨max N Na,V ∩ Va,hN.trans_le (le_max_left _ _),hV.inter hVa,⟨hq,hqa⟩,?_⟩
  intro a ha k hk P hP l
  obtain ⟨K,H,hK,hH,_,hmatch,_,_⟩ := hfamily k ((le_max_left _ _).trans hk)
  have hcover := hannulus a ha.2 k ((le_max_right _ _).trans hk)
  rw [classicalHill_frequency_differential_radius_independence P hP k (2*l+1) a (r/8) hrho hrhopi hcover]
  let c : ℂ := (Real.pi : ℂ)*(k : ℕ)
  have henergy (z : ℂ) (hz : z ∈ closedBall c (r/8)) : (z^2,a) ∈ classicalHillGapSquareDisc k r ×ˢ V := by
    have hkc : 0 < Real.pi*(k : ℕ) := by positivity
    have hrc : r ≤ Real.pi*(k : ℕ) := by
      have hk1 : (1 : ℝ) ≤ (k : ℕ) := by exact_mod_cast k.property
      nlinarith [Real.pi_pos]
    have hfreq : z ∈ ball ((Real.pi*(k : ℕ) : ℝ) : ℂ) (r/4) := by
      have hh : ‖z-c‖ ≤ r/8 := by simpa only [mem_closedBall,dist_eq_norm] using hz
      have hc : ((Real.pi*(k : ℕ) : ℝ) : ℂ) = c := by simp only [c,ofReal_mul,ofReal_natCast]
      rw [hc,mem_ball,dist_eq_norm]
      linarith
    have he := square_mem_energy_ball_of_small_frequency (Real.pi*(k : ℕ)) r hkc hr hrc z hfreq
    refine ⟨?_,ha.1⟩
    simpa only [classicalHillGapSquareDisc,ofReal_mul,ofReal_natCast] using ball_subset_closedBall he
  let E (z : ℂ) : ℂ := (K (z^2,a))^l*H (z^2,a)*P (z^2)*(2*z)
  have hE : AnalyticOnNhd ℂ E (closedBall c (r/8)) := by
    intro z hz
    have hmap : AnalyticAt ℂ (fun z : ℂ => (z^2,a)) z := (analyticAt_id.pow 2).prod analyticAt_const
    have hKz := (hK (z^2,a) (henergy z hz)).comp (f := fun z : ℂ => (z^2,a)) hmap
    have hHz := (hH (z^2,a) (henergy z hz)).comp (f := fun z : ℂ => (z^2,a)) hmap
    have hPz := (hP (z^2) (mem_univ _)).comp (f := fun z : ℂ => z^2) (analyticAt_id.pow 2)
    exact (((hKz.pow l).mul hHz).mul hPz).mul (analyticAt_const.mul analyticAt_id)
  have he (z : ℂ) (hz : z ∈ sphere c (r/8)) :
      (classicalHillContinuedPrimitive (z^2,a)+I*(k : ℂ)*Real.pi)^(2*l+1)*
        (P (z^2)/classicalHillContinuedRoot (z^2,a))*(2*z) = E z := by
    have hzd : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) :=
      closedBall_subset_closedBall hrhopi (sphere_subset_closedBall hz)
    have hd := hcover z hzd (by simpa only [c] using (mem_sphere_iff_norm.mp hz).ge)
    obtain ⟨heK,heH⟩ := hmatch (z^2,a) ⟨henergy z (sphere_subset_closedBall hz),hd⟩
    dsimp only [E]
    rw [heK,heH,pow_add,pow_mul,pow_one]
    ring
  rw [circleIntegral.integral_congr hrho.le he]
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable hrho.le countable_empty
    hE.continuousOn (fun z hz => (hE z (ball_subset_closedBall hz.1)).differentiableAt)

end NLS.KdV
