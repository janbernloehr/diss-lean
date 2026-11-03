import NLS.ComplexAnalysis.TwoZeroDeflation
import NLS.ComplexAnalysis.CircleCauchyTransform
import NLS.ComplexAnalysis.ZeroMultiset

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem circleCauchyTransform_div_two_zero_factor
    (f : ℂ → ℂ) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) {a b : ℂ}
    (ha : a ∈ ball c R) (hb : b ∈ ball c R)
    (hfa : f a = 0) (hfb : f b = 0) (hab : a = b → deriv f a = 0)
    {z : ℂ} (hz : z ∈ ball c R) :
    circleCauchyTransform (fun w => f w/((w-a)*(w-b))) c R z =
      twoZeroQuotient f a b z := by
  have hQ := analyticOnNhd_twoZeroQuotient f (closedBall c R) a b hf
    (ball_subset_closedBall ha) (ball_subset_closedBall hb)
  have he : (∮ w in C(c,R), f w/((w-a)*(w-b))/(w-z)) =
      ∮ w in C(c,R), twoZeroQuotient f a b w/(w-z) := by
    apply circleIntegral.integral_congr hR.le
    intro w hw
    have hwa : w-a ≠ 0 := sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hw ha)
    have hwb : w-b ≠ 0 := sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hw hb)
    dsimp only
    rw [twoZeroQuotient_factor f a b hfa hfb hab w]
    congr 1
    field_simp
  have hc : (∮ w in C(c,R), twoZeroQuotient f a b w/(w-z)) =
      (2 * Real.pi * I)*twoZeroQuotient f a b z := by
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using
      hQ.differentiableOn.circleIntegral_sub_inv_smul hz
  rw [circleCauchyTransform,he,hc]
  have hn : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  exact inv_mul_cancel_left₀ hn _

theorem deriv_eq_zero_of_two_zero_order
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (hfa : f a = 0)
    (hm : analyticOrderNatAt f a = 2) : deriv f a = 0 := by
  by_contra hd
  have ho := hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hfa hd
  have hn := congrArg ENat.toNat ho
  change analyticOrderNatAt f a = 1 at hn
  omega

theorem circleCauchyTransform_two_zero_unit
    (f : ℂ → ℂ) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ w ∈ sphere c R, f w ≠ 0) {a b : ℂ}
    (ha : a ∈ ball c R) (hb : b ∈ ball c R) (hfa : f a = 0) (hfb : f b = 0)
    (hm : ∀ w ∈ closedBall c R, analyticOrderNatAt f w = ({a,b} : Multiset ℂ).count w)
    {z : ℂ} (hz : z ∈ ball c R) :
    f z = (z-a)*(z-b)*circleCauchyTransform (fun w => f w/((w-a)*(w-b))) c R z ∧
    circleCauchyTransform (fun w => f w/((w-a)*(w-b))) c R z ≠ 0 := by
  have hab (he : a = b) : deriv f a = 0 := by
    apply deriv_eq_zero_of_two_zero_order (hf a (ball_subset_closedBall ha)) hfa
    simpa [he] using hm a (ball_subset_closedBall ha)
  rw [circleCauchyTransform_div_two_zero_factor f hR hf ha hb hfa hfb hab hz]
  refine ⟨twoZeroQuotient_factor f a b hfa hfb hab z,?_⟩
  obtain ⟨w,hw⟩ := (NormedSpace.sphere_nonempty (E := ℂ) (x := c)).mpr hR.le
  have hfinite := analyticOrderAt_ne_top_on_connected
    (convex_closedBall c R).isPreconnected hf
    (sphere_subset_closedBall hw) (hboundary w hw) (ball_subset_closedBall hz)
  apply twoZeroQuotient_ne_zero f (closedBall c R) a b z hf
    (ball_subset_closedBall ha) (ball_subset_closedBall hb) (ball_subset_closedBall hz) hfa hfb hab
  · intro hz0
    have hp := analyticOrderNatAt_pos_of_zero (hf z (ball_subset_closedBall hz)) hfinite hz0
    rw [hm z (ball_subset_closedBall hz)] at hp
    simpa using Multiset.count_pos.mp hp
  · exact fun _ => hm z (ball_subset_closedBall hz)

end NLS.ComplexAnalysis
