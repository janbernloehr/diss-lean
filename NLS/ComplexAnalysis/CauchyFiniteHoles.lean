import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Cauchy values in a disc with finitely many holes

The removable divided difference reduces the value formula to the existing
finite-hole contour decomposition. Inner circles retain positive orientation
and are subtracted from the outer contour.
-/

noncomputable section
open Set Metric Filter Topology Complex
namespace NLS.ComplexAnalysis

theorem analyticOnNhd_dslope_of_analytic (f : ℂ → ℂ) (U : Set ℂ) (x : ℂ)
    (hf : AnalyticOnNhd ℂ f U) (hx : x ∈ U) : AnalyticOnNhd ℂ (dslope f x) U := by
  intro z hz
  by_cases he : z=x
  · subst z
    obtain ⟨p,hp⟩ := hf x hx
    exact ⟨_,hp.has_fpower_series_dslope_fslope⟩
  · have ha : AnalyticAt ℂ (fun w => (f w-f x)/(w-x)) z :=
      ((hf z hz).sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr he)
    apply ha.congr
    filter_upwards [isOpen_ne.mem_nhds he] with w hw
    rw [dslope_of_ne f hw]
    simp only [slope,smul_eq_mul,vsub_eq_sub,div_eq_mul_inv]
    ring

theorem circleIntegral_dslope_eq (f : ℂ → ℂ) (x c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hf : ContinuousOn f (sphere c R)) (hx : x ∉ sphere c R) :
    (∮ z in C(c,R), dslope f x z) =
      (∮ z in C(c,R), f z/(z-x))-f x*(∮ z in C(c,R), (z-x)⁻¹) := by
  have hn : ∀ z ∈ sphere c R, z-x ≠ 0 :=
    fun z hz he => hx (sub_eq_zero.mp he ▸ hz)
  have hi : ContinuousOn (fun z : ℂ => (z-x)⁻¹) (sphere c R) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hn
  calc
    _ = ∮ z in C(c,R), f z/(z-x)-f x*(z-x)⁻¹ := by
      apply circleIntegral.integral_congr hR
      intro z hz
      rw [dslope_of_ne f (sub_ne_zero.mp (hn z hz))]
      simp only [slope,smul_eq_mul,vsub_eq_sub,div_eq_mul_inv]
      ring
    _ = _ := by
      have hq : CircleIntegrable (fun z => f z/(z-x)) c R :=
        (hf.div (continuousOn_id.sub continuousOn_const) hn).circleIntegrable hR
      have hi2 : CircleIntegrable (fun z => f x*(z-x)⁻¹) c R :=
        (continuousOn_const.mul hi).circleIntegrable hR
      rw [circleIntegral.integral_sub hq hi2,circleIntegral.integral_const_mul]

/-- Cauchy's value formula on a closed disc with finitely many disjoint circular holes. -/
theorem circleIntegral_cauchy_value_of_finite_holes {ι : Type*}
    (d : ℂ) (S : ℝ) (hS : 0 ≤ S) (s : Finset ι)
    (c : ι → ℂ) (r R : ι → ℝ) (f : ℂ → ℂ)
    (hr : ∀ i ∈ s, 0 < r i) (hrR : ∀ i ∈ s, r i < R i)
    (henclosed : ∀ i ∈ s, closedBall (c i) (R i) ⊆ ball d S)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (closedBall (c i) (R i)) (closedBall (c j) (R j)))
    (hf : AnalyticOnNhd ℂ f (circleHoleDomain d S s c r))
    (x : ℂ) (hx : x ∈ ball d S) (hxi : ∀ i ∈ s, x ∉ closedBall (c i) (r i)) :
    (2*(Real.pi:ℂ)*I)*f x =
      (∮ z in C(d,S), f z/(z-x)) - ∑ i ∈ s, ∮ z in C(c i,r i), f z/(z-x) := by
  have hxU : x ∈ circleHoleDomain d S s c r :=
    ⟨ball_subset_closedBall hx,fun i hi hb => hxi i hi (ball_subset_closedBall hb)⟩
  have houter : sphere d S ⊆ circleHoleDomain d S s c r := by
    intro z hz
    refine ⟨sphere_subset_closedBall hz,?_⟩
    intro i hi hzi
    exact sphere_disjoint_ball.le_bot ⟨hz,henclosed i hi
      ((closedBall_subset_closedBall (hrR i hi).le) (ball_subset_closedBall hzi))⟩
  have hinner : ∀ i ∈ s, sphere (c i) (r i) ⊆ circleHoleDomain d S s c r := by
    intro i hi z hz
    have hzi : z ∈ closedBall (c i) (R i) :=
      (closedBall_subset_closedBall (hrR i hi).le) (sphere_subset_closedBall hz)
    refine ⟨ball_subset_closedBall (henclosed i hi hzi),?_⟩
    intro j hj hzj
    by_cases hij : i=j
    · subst j
      exact sphere_disjoint_ball.le_bot ⟨hz,hzj⟩
    · exact (hdisj i hi j hj hij).le_bot ⟨hzi,
        (closedBall_subset_closedBall (hrR j hj).le) (ball_subset_closedBall hzj)⟩
  have hd := circleIntegral_eq_sum_of_finite_holes d S hS s c r R (dslope f x)
    hr hrR henclosed hdisj (analyticOnNhd_dslope_of_analytic f _ x hf hxU)
  rw [circleIntegral_dslope_eq f x d S hS (hf.continuousOn.mono houter)
    (fun hs => sphere_disjoint_ball.le_bot ⟨hs,hx⟩),circleIntegral.integral_sub_inv_of_mem_ball hx] at hd
  have he (i : ι) (hi : i ∈ s) : (∮ z in C(c i,r i), dslope f x z) =
      ∮ z in C(c i,r i), f z/(z-x) := by
    rw [circleIntegral_dslope_eq f x (c i) (r i) (hr i hi).le (hf.continuousOn.mono (hinner i hi))
      (fun hs => hxi i hi (sphere_subset_closedBall hs)),
      circleIntegral_inv_sub_eq_zero_of_notMem_closedBall (c i) x (r i) (hr i hi).le (hxi i hi),
      mul_zero,sub_zero]
  rw [Finset.sum_congr rfl he] at hd
  linear_combination -hd

end NLS.ComplexAnalysis
