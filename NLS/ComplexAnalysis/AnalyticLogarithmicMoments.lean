import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic
import NLS.ComplexAnalysis.WeightedArgumentPrinciple
import NLS.ComplexAnalysis.ZeroMultiset

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def logarithmicCircleMoment (F : ℂ × A → ℂ) (c : ℂ) (R : ℝ) (j : ℕ) (p : A) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∮ z in C(c,R), z^j * logDeriv (fun w => F (w,p)) z

theorem analyticOnNhd_logarithmicCircleMoment
    (F : ℂ × A → ℂ) (hF : AnalyticOnNhd ℂ F univ)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (j : ℕ) {V : Set A} (hV : IsOpen V)
    (hb : ∀ p ∈ V, ∀ z ∈ sphere c R, F (z,p) ≠ 0) :
    AnalyticOnNhd ℂ (logarithmicCircleMoment F c R j) V := by
  let D : Set (ℂ × A) := {t | F t ≠ 0}
  have hD : IsOpen D := isOpen_ne_fun
    (continuous_iff_continuousAt.mpr (fun t => (hF t (mem_univ _)).continuousAt)) continuous_const
  have hd : AnalyticOnNhd ℂ (fun t : ℂ × A => deriv (fun w => F (w,t.2)) t.1) D :=
    (analyticOnNhd_spectral_deriv_of_analyticOnNhd F univ isOpen_univ hF).mono (subset_univ D)
  have hg : AnalyticOnNhd ℂ
      (fun t : ℂ × A => t.1^j * logDeriv (fun w => F (w,t.2)) t.1) D := by
    intro t ht
    exact (analyticAt_fst.pow j).mul ((hd t ht).div (hF t (mem_univ _)) ht)
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic
    _ hD hg c R hR hV hb
  exact analyticOnNhd_const.mul hi

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
theorem logarithmicCircleMoment_eq_two_root_powers
    (F : ℂ × A → ℂ) (p : A) {c : ℂ} {R : ℝ} (hR : 0 < R) (j : ℕ)
    (hF : AnalyticOnNhd ℂ (fun z => F (z,p)) (closedBall c R))
    (hb : ∀ z ∈ sphere c R, F (z,p) ≠ 0)
    {a b : ℂ} (ha : a ∈ ball c R) (hb' : b ∈ ball c R)
    (hm : ∀ z ∈ closedBall c R,
      analyticOrderNatAt (fun w => F (w,p)) z = ({a,b} : Multiset ℂ).count z) :
    logarithmicCircleMoment F c R j p = a^j+b^j := by
  obtain ⟨w,hw⟩ := (NormedSpace.sphere_nonempty (E := ℂ) (x := c)).mpr hR.le
  have hfinite (z : ℂ) (hz : z ∈ closedBall c R) :
      analyticOrderAt (fun w => F (w,p)) z ≠ ⊤ :=
    analyticOrderAt_ne_top_on_connected (isConnected_closedBall hR.le).isPreconnected hF
      (sphere_subset_closedBall hw) (hb w hw) hz
  have hcover (z : ℂ) (hz : z ∈ closedBall c R) (hz0 : F (z,p) = 0) :
      z ∈ ({a,b} : Finset ℂ) := by
    have hp := analyticOrderNatAt_pos_of_zero (hF z hz) (hfinite z hz) hz0
    rw [hm z hz] at hp
    simpa using Multiset.count_pos.mp hp
  have hsum := circleIntegral_weighted_logDeriv_eq_sum hR hF
    ((analyticOnNhd_id.pow j).mono (subset_univ _)) hb hfinite ({a,b} : Finset ℂ)
    (by intro z hz; simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption) hcover
  have hs : (∑ z ∈ ({a,b} : Finset ℂ),
      (analyticOrderNatAt (fun w => F (w,p)) z : ℂ)*z^j) = a^j+b^j := by
    by_cases hab : a = b
    · subst b
      rw [Finset.pair_eq_singleton, Finset.sum_singleton, hm a (ball_subset_closedBall ha)]
      simp
      ring
    · rw [Finset.sum_pair hab, hm a (ball_subset_closedBall ha), hm b (ball_subset_closedBall hb')]
      simp [hab, Ne.symm hab]
  change (∮ z in C(c,R), z^j * logDeriv (fun w => F (w,p)) z) =
    (2 * Real.pi * I) * ∑ z ∈ ({a,b} : Finset ℂ),
      (analyticOrderNatAt (fun w => F (w,p)) z : ℂ)*z^j at hsum
  rw [logarithmicCircleMoment, hsum, hs]
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  exact inv_mul_cancel_left₀ hc _

end NLS.ComplexAnalysis
