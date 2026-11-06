import NLS.KdV.HillContinuousPrimitiveComparison
import NLS.KdV.HillHminusOneReality
import NLS.SequenceSpaces.PeriodOneRealContinuousApprox
import NLS.ComplexAnalysis.StrictTraceSheet

/-! # The actual physical sheets at every real H-minus-one potential

Real continuous Fourier approximants preserve the original source
normalization. Their strict half-plane signs pass to nonnegative signs
in the H-minus-one topology. Maximum modulus and the nonconstant actual
trace exclude equality, on both entire nonreal half-planes.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusContinuedPrimitive_re_sign_finite
    (q : PeriodOneRealHminusOne) (S : Finset ℤ) (z : ℂ) (hz : z.im ≠ 0) :
    0 < z.im*(hillHminusContinuedPrimitive (z,periodOneL2Inclusion
      (periodOneFiniteL2Approx q.val (periodOneSymmetricSupport S)))).re := by
  let a := periodOneFiniteL2Approx q.val (periodOneSymmetricSupport S)
  let Q := periodOneFiniteContinuousApprox q.val (periodOneSymmetricSupport S)
  have hreal : IsRealPeriodOneHminusOne (periodOneL2Inclusion a) := by
    intro k
    simpa only [periodOneL2Inclusion_apply] using periodOneFiniteL2Approx_real q S k
  have hdom := mem_hillHminusContinuationDomain_of_im_ne_zero (periodOneL2Inclusion a) hreal z hz
  have hLdom := (hillHminusContinuationDomain_L2_iff z a).mp hdom
  rw [hillHminusContinuedPrimitive_eq_hillL2 z a hLdom]
  have hcoef : Fourier.continuousFourierCLM Q = Coeff.periodDouble a :=
    continuousFourierCLM_periodOneFiniteContinuousApprox q.val (periodOneSymmetricSupport S)
  rw [← hcoef]
  apply hillL2ContinuedPrimitive_re_sign_continuous Q ?_ z hz
  intro t
  exact periodOneFiniteContinuousApprox_im_eq_zero q S t.val

/-- The original H-minus-one primitive has the limiting physical sign.
No uniform L2 bound or extra regularity of the approximants is assumed. -/
theorem hillHminusContinuedPrimitive_re_sign_nonneg
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : z.im ≠ 0) :
    0 ≤ z.im*(hillHminusContinuedPrimitive (z,q)).re := by
  let a : Finset ℤ → Coeff 2 := fun S =>
    periodOneFiniteL2Approx q (periodOneSymmetricSupport S)
  have ht : Tendsto (fun S => periodOneL2Inclusion (a S)) atTop (𝓝 q) := by
    have hh := (WeightedCoeff.tendsto_truncate (Weight.sobolev (-1)) 2 (by simp) q).comp
      tendsto_periodOneSymmetricSupport
    simpa only [a,periodOneL2Inclusion_finiteApprox,Function.comp_def] using hh
  have hf : AnalyticAt ℂ (fun b : PeriodOneHminusOne => hillHminusContinuedPrimitive (z,b)) q :=
    (analyticOnNhd_hillHminusContinuedPrimitive (z,q)
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hq z hz)).comp
      (f := fun b : PeriodOneHminusOne => (z,b)) (analyticAt_const.prod analyticAt_id)
  have hlim : Tendsto (fun S => z.im*(hillHminusContinuedPrimitive (z,periodOneL2Inclusion (a S))).re)
      atTop (𝓝 (z.im*(hillHminusContinuedPrimitive (z,q)).re)) :=
    tendsto_const_nhds.mul (continuous_re.continuousAt.tendsto.comp (hf.continuousAt.tendsto.comp ht))
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall fun S =>
    (hillHminusContinuedPrimitive_re_sign_finite ⟨q,hq⟩ S z hz).le)

/-- The ACTUAL free-normalized primitive is the positive-real-part sheet
on the entire upper energy half-plane, for every real H-minus-one input. -/
theorem hillHminusContinuedPrimitive_re_pos
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : 0 < z.im) :
    0 < (hillHminusContinuedPrimitive (z,q)).re := by
  apply re_pos_of_nonneg_of_nonconstant_cosh_trace
    (fun w => hillHminusContinuedPrimitive (w,q)) (hillHminusDiscriminant q)
    {w : ℂ | 0 < w.im} (isOpen_lt continuous_const continuous_im)
    ((analyticOnNhd_hillHminusContinuedPrimitive_off_real q hq).mono
      (fun _ hw => ne_of_gt hw)) ?_ ?_ (hillHminusDiscriminant_not_constant q) ?_ z hz
  · intro w _
    exact (analyticOnNhd_hillHminusDiscriminant_joint (w,q) (mem_univ _)).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  · intro w hw
    exact (hillHminusContinuedPrimitive_trace (w,q)
      (mem_hillHminusContinuationDomain_of_im_ne_zero q hq w (ne_of_gt hw))).1
  · intro w hw
    have he := hillHminusContinuedPrimitive_re_sign_nonneg q hq w (ne_of_gt hw)
    change 0 < w.im at hw
    nlinarith

/-- The ACTUAL free-normalized primitive is the negative-real-part sheet
on the entire lower energy half-plane, with no high-energy restriction. -/
theorem hillHminusContinuedPrimitive_re_neg
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : z.im < 0) :
    (hillHminusContinuedPrimitive (z,q)).re < 0 := by
  have he : 0 < (-hillHminusContinuedPrimitive (z,q)).re := by
    apply re_pos_of_nonneg_of_nonconstant_cosh_trace
      (fun w => -hillHminusContinuedPrimitive (w,q)) (hillHminusDiscriminant q)
      {w : ℂ | w.im < 0} (isOpen_lt continuous_im continuous_const)
      (((analyticOnNhd_hillHminusContinuedPrimitive_off_real q hq).mono
        (fun _ hw => ne_of_lt hw)).neg) ?_ ?_ (hillHminusDiscriminant_not_constant q) ?_ z hz
    · intro w _
      exact (analyticOnNhd_hillHminusDiscriminant_joint (w,q) (mem_univ _)).comp
        (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
    · intro w hw
      simpa only [cosh_neg] using (hillHminusContinuedPrimitive_trace (w,q)
        (mem_hillHminusContinuationDomain_of_im_ne_zero q hq w (ne_of_lt hw))).1
    · intro w hw
      have he := hillHminusContinuedPrimitive_re_sign_nonneg q hq w (ne_of_lt hw)
      change w.im < 0 at hw
      simp only [neg_re]
      nlinarith
  simpa only [neg_re,neg_pos] using he

theorem hillHminusContinuedPrimitive_re_sign
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (hz : z.im ≠ 0) :
    0 < z.im*(hillHminusContinuedPrimitive (z,q)).re := by
  rcases lt_or_gt_of_ne hz with h | h
  · exact mul_pos_of_neg_of_neg h (hillHminusContinuedPrimitive_re_neg q hq z h)
  · exact mul_pos h (hillHminusContinuedPrimitive_re_pos q hq z h)

end NLS.KdV
