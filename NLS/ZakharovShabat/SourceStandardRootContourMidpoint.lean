import NLS.ZakharovShabat.SourceStandardRootContourBasic
import Mathlib.Analysis.Complex.MeanValue

/-!
# Diagonal inverse-root contour integral on midpoint circles

Circle inversion turns the integral of the reciprocal normalized root
into a circle average of an analytic function near zero. The mean-value
theorem gives the constant term, proving the diagonal value `−1` for
any midpoint-centered circle whose radius exceeds half the gap norm,
including noncollapsed gaps.
-/

open Complex Metric Set
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem circleAverage_inverse_pulled (H : ℂ → ℂ) (t : ℂ) (R : ℝ) :
    Real.circleAverage (fun z => H ((z-t)⁻¹)) t R =
      Real.circleAverage H 0 R⁻¹ := by
  rw [Real.circleAverage_eq_circleAverage_zero_one]
  have heq : (fun u : ℂ => H (((R:ℂ)*u+t-t)⁻¹)) =
      (fun u : ℂ => H (((R⁻¹:ℝ):ℂ)*u⁻¹)) := by
    funext u
    simp only [add_sub_cancel_right]
    rw [mul_inv_rev, Complex.ofReal_inv]
    simp [mul_comm]
  rw [heq]
  calc
    Real.circleAverage (fun u : ℂ => H (((R⁻¹:ℝ):ℂ)*u⁻¹)) 0 1 =
        Real.circleAverage (fun u : ℂ => H (((R⁻¹:ℝ):ℂ)*u)) 0 1 := by
          simpa using (Real.circleAverage_zero_one_congr_inv
            (f := fun u : ℂ => H (((R⁻¹:ℝ):ℂ)*u)))
    _ = Real.circleAverage H 0 R⁻¹ := by
      simpa only [Complex.ofReal_inv, mul_zero, add_zero] using
        (Real.circleAverage_eq_circleAverage_zero_one
          (f := H) (c := 0) (R := R⁻¹)).symm

private theorem circleIntegral_inverse_pulled (H : ℂ → ℂ) (t : ℂ)
    (R : ℝ) (hR : 0 < R) :
    (∮ z in C(t, R), (z-t)⁻¹ * H ((z-t)⁻¹)) =
      (2*Real.pi*Complex.I) * Real.circleAverage H 0 R⁻¹ := by
  let K : ℂ := 2*Real.pi*Complex.I
  let J : ℂ := ∮ z in C(t, R), (z-t)⁻¹ * H ((z-t)⁻¹)
  have h := Real.circleAverage_eq_circleIntegral
    (f := fun z : ℂ => H ((z-t)⁻¹)) (c := t) (R := R) hR.ne'
  rw [circleAverage_inverse_pulled] at h
  change Real.circleAverage H 0 R⁻¹ = K⁻¹ * J at h
  have hK : K ≠ 0 := by dsimp [K]; simp [Real.pi_ne_zero]
  change J = K * Real.circleAverage H 0 R⁻¹
  calc
    J = K * (K⁻¹ * J) := by rw [← mul_assoc, mul_inv_cancel₀ hK, one_mul]
    _ = K * Real.circleAverage H 0 R⁻¹ := by rw [← h]

private theorem circleIntegral_inverse_pulled_holomorphic (H : ℂ → ℂ) (t : ℂ)
    (R : ℝ) (hR : 0 < R)
    (hH : DiffContOnCl ℂ H (Metric.ball (0:ℂ) |R⁻¹|)) :
    (∮ z in C(t, R), (z-t)⁻¹ * H ((z-t)⁻¹)) =
      (2*Real.pi*Complex.I) * H 0 := by
  rw [circleIntegral_inverse_pulled H t R hR, hH.circleAverage]


private theorem normalizedRoot_inv_circle_form (t g z : ℂ) (hz : z ≠ t) :
    (normalizedStandardRoot t g z)⁻¹ =
      -((z-t)⁻¹) * (Complex.sqrt (1-(g/4)*((z-t)⁻¹)^2))⁻¹ := by
  have hzt : z-t ≠ 0 := sub_ne_zero.mpr hz
  have htz : t-z ≠ 0 := sub_ne_zero.mpr hz.symm
  have hrad : 1-g/(4*(t-z)^2) = 1-(g/4)*((z-t)⁻¹)^2 := by
    field_simp [hzt, htz]
    ring
  unfold normalizedStandardRoot
  rw [hrad, mul_inv_rev]
  have hinv : (t-z)⁻¹ = -((z-t)⁻¹) := by
    calc
      (t-z)⁻¹ = (-(z-t))⁻¹ := congrArg Inv.inv (by ring)
      _ = -((z-t)⁻¹) := inv_neg
  rw [hinv]
  ring

private theorem circleIntegral_normalizedRoot_inv_of_holomorphic (t g : ℂ)
    (R : ℝ) (hR : 0 < R)
    (hH : DiffContOnCl ℂ
      (fun u : ℂ => (Complex.sqrt (1-(g/4)*u^2))⁻¹)
      (Metric.ball (0:ℂ) |R⁻¹|)) :
    (∮ z in C(t, R), (normalizedStandardRoot t g z)⁻¹) =
      -(2*Real.pi*Complex.I) := by
  let H : ℂ → ℂ := fun u => (Complex.sqrt (1-(g/4)*u^2))⁻¹
  have heq : (∮ z in C(t, R), (normalizedStandardRoot t g z)⁻¹) =
      ∮ z in C(t, R), -((z-t)⁻¹) * H ((z-t)⁻¹) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    exact normalizedRoot_inv_circle_form t g z (by
      intro he
      have hbad := (mem_sphere.mp hz)
      rw [he, dist_self] at hbad
      linarith)
  rw [heq]
  have hneg : (∮ z in C(t, R), -((z-t)⁻¹) * H ((z-t)⁻¹)) =
      -(∮ z in C(t, R), (z-t)⁻¹ * H ((z-t)⁻¹)) := by
    have heq' : (fun z : ℂ => -((z-t)⁻¹) * H ((z-t)⁻¹)) =
        (fun z : ℂ => (-1)*((z-t)⁻¹ * H ((z-t)⁻¹))) := by
      funext z; ring
    rw [heq', circleIntegral.integral_const_mul]
    ring
  rw [hneg, circleIntegral_inverse_pulled_holomorphic H t R hR hH]
  simp [H]

private theorem circleIntegral_normalizedRoot_inv_of_slit (t g : ℂ)
    (R : ℝ) (hR : 0 < R)
    (hslit : ∀ u ∈ Metric.closedBall (0:ℂ) |R⁻¹|,
      1-(g/4)*u^2 ∈ Complex.slitPlane) :
    (∮ z in C(t, R), (normalizedStandardRoot t g z)⁻¹) =
      -(2*Real.pi*Complex.I) := by
  let rad : ℂ → ℂ := fun u => 1-(g/4)*u^2
  let H : ℂ → ℂ := fun u => (Complex.sqrt (rad u))⁻¹
  have hAt (u : ℂ) (hu : u ∈ Metric.closedBall (0:ℂ) |R⁻¹|) :
      DifferentiableAt ℂ H u := by
    have hru : rad u ∈ Complex.slitPlane := hslit u hu
    have hru0 : rad u ≠ 0 := by
      intro he
      exact Complex.zero_notMem_slitPlane (he ▸ hru)
    have hsqrt0 : Complex.sqrt (rad u) ≠ 0 := by
      rw [sqrt_eq_exp hru0]
      exact Complex.exp_ne_zero _
    have hrad : DifferentiableAt ℂ rad u := by
      dsimp [rad]
      fun_prop
    exact ((Complex.differentiableAt_sqrt hru).comp u hrad).inv hsqrt0
  have hd : DifferentiableOn ℂ H (Metric.closedBall (0:ℂ) |R⁻¹|) := by
    intro u hu
    exact (hAt u hu).differentiableWithinAt
  have hH : DiffContOnCl ℂ H (Metric.ball (0:ℂ) |R⁻¹|) :=
    DiffContOnCl.mk_ball (hd.mono Metric.ball_subset_closedBall) hd.continuousOn
  exact circleIntegral_normalizedRoot_inv_of_holomorphic t g R hR hH

/-- The reciprocal normalized root has integral `−2πi` on a
midpoint circle whenever its radius dominates the quadratic gap. -/
theorem circleIntegral_normalizedRoot_inv_of_radius (t g : ℂ)
    (R : ℝ) (hR : 0 < R)
    (hsmall : ‖g‖*(R⁻¹)^2 < 4) :
    (∮ z in C(t, R), (normalizedStandardRoot t g z)⁻¹) =
      -(2*Real.pi*Complex.I) := by
  apply circleIntegral_normalizedRoot_inv_of_slit t g R hR
  intro u hu
  have hnormu : ‖u‖ ≤ R⁻¹ := by
    simpa only [mem_closedBall, dist_zero_right, abs_of_pos (inv_pos.mpr hR)] using hu
  have hnorm : ‖(g/4)*u^2‖ = ‖g‖/4*‖u‖^2 := by
    simp only [norm_mul, norm_div, norm_pow, norm_ofNat]
  have hsq : ‖u‖^2 ≤ (R⁻¹)^2 := by
    exact pow_le_pow_left₀ (norm_nonneg u) hnormu 2
  have hbound : ‖(g/4)*u^2‖ ≤ ‖g‖/4*(R⁻¹)^2 := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hlt : ‖(g/4)*u^2‖ < 1 := by
    have hsmall' : ‖g‖/4*(R⁻¹)^2 < 1 := by nlinarith [hsmall]
    exact lt_of_le_of_lt hbound hsmall'
  simpa only [sub_eq_add_neg, norm_neg] using
    Complex.mem_slitPlane_of_norm_lt_one (z := -((g/4)*u^2)) (by simpa using hlt)

/-- The source standard-root diagonal integral on every midpoint circle
strictly containing the canonical gap segment. -/
theorem circleIntegral_sourceStandardRoot_inv_midpoint_radius
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (t : ℂ)
    (ht : t = canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n)
    (R : ℝ) (hR : 0 < R)
    (hgapR : ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n‖/2 < R) :
    (∮ z in C(t, R), (sourceStandardRoot hp hp1 ψ n z)⁻¹) =
      -(2*Real.pi*Complex.I) := by
  subst t
  let d := canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have hdR : ‖d‖ < 2*R := by dsimp [d] at *; linarith
  have hsq : ‖d‖^2 < (2*R)^2 :=
    (sq_lt_sq₀ (norm_nonneg d) (by positivity)).2 hdR
  have hsmall : ‖d^2‖*(R⁻¹)^2 < 4 := by
    rw [norm_pow, inv_pow, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (sq_pos_of_pos hR)).2
    nlinarith [hsq]
  simpa only [sourceStandardRoot, d] using
    circleIntegral_normalizedRoot_inv_of_radius
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n) (d^2) R hR hsmall

/-- The normalized diagonal value is `−1` on every midpoint circle
strictly containing the canonical gap segment. -/
theorem normalized_circleIntegral_sourceStandardRoot_inv_midpoint_radius
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (t : ℂ)
    (ht : t = canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n)
    (R : ℝ) (hR : 0 < R)
    (hgapR : ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n‖/2 < R) :
    (2*Real.pi*Complex.I)⁻¹ *
      (∮ z in C(t, R), (sourceStandardRoot hp hp1 ψ n z)⁻¹) = -1 := by
  rw [circleIntegral_sourceStandardRoot_inv_midpoint_radius
    hp hp1 ψ n t ht R hR hgapR]
  have hnonzero : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  calc
    (2*Real.pi*Complex.I)⁻¹ * -(2*Real.pi*Complex.I) =
        -((2*Real.pi*Complex.I)⁻¹ * (2*Real.pi*Complex.I)) := by ring
    _ = -1 := by rw [inv_mul_cancel₀ hnonzero]

end NLS.ZakharovShabat
