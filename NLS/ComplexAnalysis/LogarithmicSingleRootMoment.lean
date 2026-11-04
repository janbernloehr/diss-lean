import NLS.ComplexAnalysis.AnalyticLogarithmicMoments

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



variable {A : Type}

theorem logarithmicCircleMoment_eq_single_root_power
    (F : ℂ × A → ℂ) (p : A) {c : ℂ} {R : ℝ} (hR : 0 < R) (j : ℕ)
    (hF : AnalyticOnNhd ℂ (fun z => F (z,p)) (closedBall c R))
    (hb : ∀ z ∈ sphere c R, F (z,p) ≠ 0)
    {a : ℂ} (ha : a ∈ ball c R)
    (hm : ∀ z ∈ closedBall c R,
      analyticOrderNatAt (fun w => F (w,p)) z = if z=a then 1 else 0) :
    logarithmicCircleMoment F c R j p = a^j := by
  obtain ⟨w,hw⟩ := (NormedSpace.sphere_nonempty (E := ℂ) (x := c)).mpr hR.le
  have hfinite (z : ℂ) (hz : z ∈ closedBall c R) :
      analyticOrderAt (fun w => F (w,p)) z ≠ ⊤ :=
    analyticOrderAt_ne_top_on_connected (isConnected_closedBall hR.le).isPreconnected hF
      (sphere_subset_closedBall hw) (hb w hw) hz
  have hcover (z : ℂ) (hz : z ∈ closedBall c R) (hz0 : F (z,p) = 0) :
      z ∈ ({a} : Finset ℂ) := by
    have hp := analyticOrderNatAt_pos_of_zero (hF z hz) (hfinite z hz) hz0
    rw [hm z hz] at hp
    by_cases he : z=a
    · simpa only [Finset.mem_singleton] using he
    · simp only [if_neg he] at hp
      omega
  have hsum := circleIntegral_weighted_logDeriv_eq_sum hR hF
    ((analyticOnNhd_id.pow j).mono (subset_univ _)) hb hfinite ({a} : Finset ℂ)
    (by intro z hz; simpa only [Finset.mem_singleton.mp hz] using ha) hcover
  change (∮ z in C(c,R), z^j * logDeriv (fun w => F (w,p)) z) =
    (2 * Real.pi * I) * ∑ z ∈ ({a} : Finset ℂ),
      (analyticOrderNatAt (fun w => F (w,p)) z : ℂ)*z^j at hsum
  rw [Finset.sum_singleton,hm a (ball_subset_closedBall ha),if_pos rfl,Nat.cast_one,one_mul] at hsum
  rw [logarithmicCircleMoment,hsum]
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  exact inv_mul_cancel_left₀ hc _

end NLS.ComplexAnalysis
