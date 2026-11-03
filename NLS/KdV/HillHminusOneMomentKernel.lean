import NLS.KdV.HillHminusOneNormalizedMoments
import NLS.SequenceSpaces.QuadraticPoleKernel
import NLS.ComplexAnalysis.CriticalBasisPowerPeriods

/-! # Direct Hilbert kernels for actual rough Hill moments

Only selected critical energy growth and contour separation are used. The
Hilbert kernel does not divide by the discriminant derivative.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

def hillHminusSquaredCriticalKernel (C : HillHminusMiuraChart) (N : ℕ)
    (q : PeriodOneHminusOne) (lambda : ℂ) : NLS.Coeff 2 :=
  NLS.Coeff.quadraticPoleKernel (fun j => hillHminusUniformCriticalPoint C N j q) lambda

def hillHminusMomentKernelVector (C : HillHminusMiuraChart) (N : ℕ) (k : ℕ+) (m : ℕ)
    (q : PeriodOneHminusOne) : NLS.Coeff 2 :=
  ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
    ((hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)) •
      hillHminusSquaredCriticalKernel C N q (z^2)

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem selected_critical_denominator_ne_zero (j k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
    z^2-hillHminusUniformCriticalPoint C N j q ≠ 0 := by
  by_cases hjk : j = k
  · subst j
    exact norm_pos_iff.mp ((by positivity : 0 < Real.pi^2/8*(k : ℝ)).trans_le
      (D.diagonal_separation k q hq z hz))
  · exact norm_pos_iff.mp ((mul_pos (by positivity)
      (abs_pos.mpr (positiveIndex_squared_sub_ne_zero k j (Ne.symm hjk)))).trans_le
        (D.offDiagonal_separation j k hjk q hq z hz))

theorem squaredCriticalKernel_spec (q : PeriodOneHminusOne) (hq : q ∈ V) :
    (∀ lambda ∈ NLS.Coeff.quadraticPoleDomain (fun j => hillHminusUniformCriticalPoint C N j q),
      ∀ j : ℤ, hillHminusSquaredCriticalKernel C N q lambda j =
        NLS.Coeff.quadraticPoleCoordinates (fun j => hillHminusUniformCriticalPoint C N j q) lambda j) ∧
      AnalyticOnNhd ℂ (hillHminusSquaredCriticalKernel C N q)
        (NLS.Coeff.quadraticPoleDomain (fun j => hillHminusUniformCriticalPoint C N j q)) :=
  NLS.Coeff.quadraticPoleKernel_spec _ (Real.pi^2/4) (by positivity)
    (fun j => D.critical_energy_growth j q hq)

theorem momentKernel_contour_integrable (k : ℕ+) (m : ℕ)
    (q : PeriodOneHminusOne) (hq : q ∈ V) :
    CircleIntegrable (fun z : ℂ =>
      ((hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)) •
        hillHminusSquaredCriticalKernel C N q (z^2))
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
  have hf : AnalyticOnNhd ℂ (fun z => hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)
      (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z hz
    exact ((analyticOnNhd_hillHminusContinuedPrimitive (z^2,q) (D.cover k q hq z hz)).comp
      (f := fun z : ℂ => (z^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)).add analyticAt_const
  have hw : AnalyticOnNhd ℂ (fun z => hillHminusSquaredCriticalKernel C N q (z^2))
      (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z hz
    exact (D.squaredCriticalKernel_spec q hq).2 (z^2)
      (fun j => D.selected_critical_denominator_ne_zero j k q hq z hz) |>.comp
        (f := fun z : ℂ => z^2) (analyticAt_id.pow 2)
  exact ((((hf.pow (m+1)).mul (analyticOnNhd_const.mul analyticOnNhd_id)).smul hw).continuousOn).circleIntegrable (by positivity)

theorem momentKernelVector_positive (k j : ℕ+) (m : ℕ)
    (q : PeriodOneHminusOne) (hq : q ∈ V) :
    hillHminusMomentKernelVector C N k m q (j : ℤ) = (j : ℂ)*
      ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
        (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)/
          (z^2-hillHminusUniformCriticalPoint C N j q)^2 := by
  change (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (j : ℤ)) (hillHminusMomentKernelVector C N k m q) = _
  unfold hillHminusMomentKernelVector
  rw [map_circleIntegral _ (D.momentKernel_contour_integrable k m q hq),← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr (by positivity)
  intro z hz
  simp only [map_smul,smul_eq_mul]
  change _*hillHminusSquaredCriticalKernel C N q (z^2) (j : ℤ) = _
  have he := NLS.Coeff.quadraticPoleKernel_positive _ (Real.pi^2/4) (by positivity)
    (fun j => D.critical_energy_growth j q hq) (z^2)
    (fun i => D.selected_critical_denominator_ne_zero i k q hq z hz) j
  rw [show hillHminusSquaredCriticalKernel C N q (z^2) (j : ℤ) = _ from he]
  ring

theorem momentKernelVector_nonpositive (k : ℕ+) (m : ℕ)
    (q : PeriodOneHminusOne) (hq : q ∈ V) (j : ℤ) (hj : j ≤ 0) :
    hillHminusMomentKernelVector C N k m q j = 0 := by
  change (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j) (hillHminusMomentKernelVector C N k m q) = _
  unfold hillHminusMomentKernelVector
  rw [map_circleIntegral _ (D.momentKernel_contour_integrable k m q hq)]
  have heq : (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 j)
        (((hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^(m+1)*(2*z)) •
          hillHminusSquaredCriticalKernel C N q (z^2))) =
      (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4), (0 : ℂ)) := by
    apply circleIntegral.integral_congr (by positivity)
    intro z hz
    simp only [map_smul,smul_eq_mul]
    change _*hillHminusSquaredCriticalKernel C N q (z^2) j = 0
    rw [(D.squaredCriticalKernel_spec q hq).1 (z^2)
      (fun i => D.selected_critical_denominator_ne_zero i k q hq z hz) j]
    simp only [NLS.Coeff.quadraticPoleCoordinates,dif_neg (not_lt.mpr hj),mul_zero]
  rw [heq]
  simp only [circleIntegral,smul_zero,intervalIntegral.integral_zero]

theorem numerator_power_period_eq_kernel (j k : ℕ+) (m : ℕ)
    (q : PeriodOneHminusOne) (hq : q ∈ V) :
    (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      (hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi)^m*
        (hillHminusUniformNumerator C N j (z^2,q)/hillHminusContinuedRoot (z^2,q))*(2*z)) =
      (2*(Real.pi : ℂ))/(m+1)*hillHminusMomentKernelVector C N k m q (j : ℤ) := by
  rw [D.momentKernelVector_positive k j m q hq]
  let F (z : ℂ) := hillHminusContinuedPrimitive (z^2,q)+I*(k : ℂ)*Real.pi
  have hF : AnalyticOnNhd ℂ F (sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) := by
    intro z hz
    exact ((analyticOnNhd_hillHminusContinuedPrimitive (z^2,q) (D.cover k q hq z hz)).comp
      (f := fun z : ℂ => (z^2,q)) ((analyticAt_id.pow 2).prod analyticAt_const)).add analyticAt_const
  have hDF (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4)) :
      deriv F z = (deriv (hillHminusDiscriminant q) (z^2)/hillHminusContinuedRoot (z^2,q))*(2*z) := by
    have hsq : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by simpa using! (hasDerivAt_id z).pow 2
    exact ((hasDerivAt_hillHminusContinuedPrimitive (z^2,q) (D.cover k q hq z hz)).comp z hsq |>.add_const _).deriv
  have he := critical_basis_power_period_eq_primitive F
    (fun lambda => hillHminusUniformNumerator C N j (lambda,q))
    (fun lambda => hillHminusContinuedRoot (lambda,q)) (deriv (hillHminusDiscriminant q))
    (hillHminusUniformCriticalPoint C N j q) (j : ℂ) _ _ (by positivity) m hF
    (D.numerator_factor j q hq) hDF (D.selected_critical_denominator_ne_zero j k q hq)
  exact he.trans (by ring)

end HillHminusUniformPeriodData
end NLS.KdV
