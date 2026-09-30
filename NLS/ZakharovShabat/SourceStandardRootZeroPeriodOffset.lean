import NLS.ZakharovShabat.SourceStandardRootFirstMoment
import NLS.ZakharovShabat.SourceStandardRootInverseCorrection
import NLS.ZakharovShabat.SourcePsiNearFreeCollapsedGap
import Mathlib.Analysis.Calculus.DSlope

/-!
# Midpoint offset identities from a vanishing standard-root period

Subtract the analytic factor's value at the midpoint. The affine
standard-root moment identifies the remaining period with the root
offset. Its collapsed-gap Cauchy period is zero, so the same offset is
exactly the reciprocal-root correction applied to the centered factor.
The dslope form is equation (2.33) in the proof of Lemma 12.12.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Subtracting the regular factor's midpoint value isolates the
root offset in a vanishing weighted standard-root contour. -/
theorem sourceStandardRoot_zero_period_centered_factor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c σ : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hzero : (∮ z in C(c,R), ((σ-z)/sourceStandardRoot hp hp1 ψ m z)*f z) = 0) :
    (2*Real.pi*I : ℂ)*(σ-sourceStandardRootMidpoint hp hp1 ψ m)*
      f (sourceStandardRootMidpoint hp hp1 ψ m) =
        ∮ z in C(c,R), ((σ-z)/sourceStandardRoot hp hp1 ψ m z)*
          (f z-f (sourceStandardRootMidpoint hp hp1 ψ m)) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let w := sourceStandardRoot hp hp1 ψ m
  let A : ℂ → ℂ := fun z => (σ-z)/w z
  have havoid z (hz : z ∈ sphere c R) : z ∉ sourcePeriodicSegment hp hp1 ψ m := by
    intro hzin
    exact (ne_of_lt (mem_ball.mp (hseg hzin))) (mem_sphere.mp hz)
  have hinv : ContinuousOn (fun z => (w z)⁻¹) (sphere c R) := by
    intro z hz
    exact (sourceStandardRoot_inv_analyticAt hp hp1 ψ m z (havoid z hz)).continuousAt.continuousWithinAt
  have hA : ContinuousOn A (sphere c R) := by
    change ContinuousOn (fun z => (σ-z)*(w z)⁻¹) (sphere c R)
    exact (continuousOn_const.sub continuousOn_id).mul hinv
  have hAint := hA.circleIntegrable hR.le
  have hEint : CircleIntegrable (fun z => A z*(f z-f τ)) c R :=
    (hA.mul ((hf.continuousOn.mono sphere_subset_closedBall).sub
      continuousOn_const)).circleIntegrable hR.le
  have hCint : CircleIntegrable (fun z => f τ*A z) c R := by
    have h := hAint.const_smul (a := f τ)
    change CircleIntegrable (fun z => f τ*A z) c R at h
    exact h
  have hsplit : (∮ z in C(c,R), A z*f z) =
      f τ*(∮ z in C(c,R), A z) + (∮ z in C(c,R), A z*(f z-f τ)) := by
    rw [← circleIntegral.integral_const_mul,← circleIntegral.integral_add hCint hEint]
    apply circleIntegral.integral_congr hR.le
    intro z _
    ring
  have hmoment := circleIntegral_affine_div_sourceStandardRoot hp hp1 ψ m c σ R hR hseg
  change (∮ z in C(c,R), A z) = -(2*Real.pi*I : ℂ)*(σ-τ) at hmoment
  change (∮ z in C(c,R), A z*f z) = 0 at hzero
  rw [hzero,hmoment] at hsplit
  change (2*Real.pi*I : ℂ)*(σ-τ)*f τ = ∮ z in C(c,R), A z*(f z-f τ)
  linear_combination hsplit

/-- The exact first-order remainder identity (2.33), using the actual
divided difference, including its filled value at the midpoint. -/
theorem sourceStandardRoot_zero_period_dslope_identity
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c σ : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hzero : (∮ z in C(c,R), ((σ-z)/sourceStandardRoot hp hp1 ψ m z)*f z) = 0) :
    (2*Real.pi*I : ℂ)*(σ-sourceStandardRootMidpoint hp hp1 ψ m)*
      f (sourceStandardRootMidpoint hp hp1 ψ m) =
        ∮ z in C(c,R),
          ((σ-z)*(z-sourceStandardRootMidpoint hp hp1 ψ m)/sourceStandardRoot hp hp1 ψ m z)*
            dslope f (sourceStandardRootMidpoint hp hp1 ψ m) z := by
  rw [sourceStandardRoot_zero_period_centered_factor hp hp1 ψ m c σ R hR hseg f hf hzero]
  apply circleIntegral.integral_congr hR.le
  intro z _
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  have hlin : (z-τ)*dslope f τ z = f z-f τ := by
    simpa only [smul_eq_mul,vsub_eq_sub] using sub_smul_dslope f τ z
  change ((σ-z)/sourceStandardRoot hp hp1 ψ m z)*(f z-f τ) = _
  rw [← hlin]
  simp only [div_eq_mul_inv]
  ring

/-- A vanishing actual period identifies the root offset exactly
with the quadratic reciprocal-root correction of the centered factor. -/
theorem sourceStandardRoot_zero_period_inverse_correction_identity
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c σ : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hzero : (∮ z in C(c,R), ((σ-z)/sourceStandardRoot hp hp1 ψ m z)*f z) = 0) :
    (2*Real.pi*I : ℂ)*(σ-sourceStandardRootMidpoint hp hp1 ψ m)*
      f (sourceStandardRootMidpoint hp hp1 ψ m) =
        ∮ z in C(c,R), ((σ-z)*(f z-f (sourceStandardRootMidpoint hp hp1 ψ m)))*
          ((sourceStandardRoot hp hp1 ψ m z)⁻¹-
            (sourceStandardRootMidpoint hp hp1 ψ m-z)⁻¹) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let w := sourceStandardRoot hp hp1 ψ m
  let e : ℂ → ℂ := fun z => f z-f τ
  have he : AnalyticOnNhd ℂ e (closedBall c R) := hf.sub analyticOnNhd_const
  have hτ : τ ∈ ball c R := hseg (sourcePeriodicMidpoint_mem_segment hp hp1 ψ m)
  have hezero : (∮ z in C(c,R), ((σ-z)/(τ-z))*e z) = 0 := by
    rw [circleIntegral_collapsedGap_ratio_of_mem_ball c τ σ R hR hτ e he]
    simp only [e,sub_self,mul_zero]
  have havoid z (hz : z ∈ sphere c R) : z ∉ sourcePeriodicSegment hp hp1 ψ m := by
    intro hzin
    exact (ne_of_lt (mem_ball.mp (hseg hzin))) (mem_sphere.mp hz)
  have hwcont : ContinuousOn (fun z => (w z)⁻¹) (sphere c R) := by
    intro z hz
    exact (sourceStandardRoot_inv_analyticAt hp hp1 ψ m z (havoid z hz)).continuousAt.continuousWithinAt
  have hlcont : ContinuousOn (fun z : ℂ => (τ-z)⁻¹) (sphere c R) := by
    apply ContinuousOn.inv₀ (continuousOn_const.sub continuousOn_id)
    intro z hz heq
    have heq' : τ = z := sub_eq_zero.mp heq
    exact (ne_of_lt (mem_ball.mp (heq' ▸ hτ))) (mem_sphere.mp hz)
  have hP : ContinuousOn (fun z : ℂ => (σ-z)*e z) (sphere c R) :=
    (continuousOn_const.sub continuousOn_id).mul (he.continuousOn.mono sphere_subset_closedBall)
  have hWint := (hP.mul hwcont).circleIntegrable hR.le
  have hLint := (hP.mul hlcont).circleIntegrable hR.le
  have hcorr : (∮ z in C(c,R), ((σ-z)*e z)*((w z)⁻¹-(τ-z)⁻¹)) =
      (∮ z in C(c,R), ((σ-z)/w z)*e z) - (∮ z in C(c,R), ((σ-z)/(τ-z))*e z) := by
    have hWint' : CircleIntegrable (fun z => ((σ-z)/w z)*e z) c R := by
      convert hWint using 1
      funext z
      simp only [div_eq_mul_inv,Pi.mul_apply]
      ring
    have hLint' : CircleIntegrable (fun z => ((σ-z)/(τ-z))*e z) c R := by
      convert hLint using 1
      funext z
      simp only [div_eq_mul_inv,Pi.mul_apply]
      ring
    rw [← circleIntegral.integral_sub hWint' hLint']
    apply circleIntegral.integral_congr hR.le
    intro z _
    simp only [div_eq_mul_inv]
    ring
  rw [hcorr,hezero,sub_zero]
  exact sourceStandardRoot_zero_period_centered_factor hp hp1 ψ m c σ R hR hseg f hf hzero

end NLS.ZakharovShabat
