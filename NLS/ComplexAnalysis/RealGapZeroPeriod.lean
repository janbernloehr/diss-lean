import NLS.ComplexAnalysis.RealIntegralZero
import NLS.ComplexAnalysis.CosineZeroPeriod
import NLS.ComplexAnalysis.AnalyticTwoZeroRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis



theorem exists_gap_zero_of_real_zero_period
    (g Q : ℂ → ℂ) (τ δ c : ℂ) (r R : ℝ)
    (hδ : δ ≠ 0) (hr : 0 < r) (hrR : r < R)
    (hgap : segment ℝ (τ-δ) (τ+δ) ⊆ ball c r)
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hQ : AnalyticOnNhd ℂ Q (closedBall c R \ segment ℝ (τ-δ) (τ+δ)))
    (hsq : ∀ z ∈ closedBall c R \ segment ℝ (τ-δ) (τ+δ),
      Q z^2 = (τ-δ-z)*(τ+δ-z))
    (hperiod : (∮ z in C(c,r), g z/Q z) = 0)
    (hreal : ∀ z ∈ segment ℝ (τ-δ) (τ+δ), (g z).im = 0) :
    ∃ z ∈ segment ℝ (τ-δ) (τ+δ), g z = 0 := by
  have hmean := integral_cosineGapPoint_eq_zero_of_zero_period
    g Q τ δ c r R hδ hr hrR hgap hg hQ hsq hperiod
  have hc : ContinuousOn (fun θ : ℝ => g (cosineGapPoint τ δ (θ:ℂ)))
      (Icc 0 Real.pi) := by
    apply hg.continuousOn.comp (by unfold cosineGapPoint; fun_prop)
    intro θ _
    exact ball_subset_closedBall (ball_subset_ball hrR.le
      (hgap (cosineGapPoint_real_mem_segment τ δ θ)))
  have hri := Complex.reCLM.intervalIntegral_comp_comm (μ := volume)
    (hc.intervalIntegrable_of_Icc Real.pi_pos.le)
  change (∫ θ in (0:ℝ)..Real.pi, (g (cosineGapPoint τ δ (θ:ℂ))).re) =
    (∫ θ in (0:ℝ)..Real.pi, g (cosineGapPoint τ δ (θ:ℂ))).re at hri
  rw [hmean,Complex.zero_re] at hri
  obtain ⟨θ,_,hθ⟩ := exists_zero_of_continuousOn_integral_eq_zero
    (fun θ : ℝ => (g (cosineGapPoint τ δ (θ:ℂ))).re) 0 Real.pi Real.pi_pos
    (Complex.continuous_re.comp_continuousOn hc) hri
  refine ⟨cosineGapPoint τ δ (θ:ℂ),cosineGapPoint_real_mem_segment τ δ θ,?_⟩
  apply Complex.ext
  · exact hθ
  · exact hreal _ (cosineGapPoint_real_mem_segment τ δ θ)

theorem exists_gap_zero_of_rotated_zero_period
    (g Q : ℂ → ℂ) (τ δ c α : ℂ) (r R : ℝ)
    (hδ : δ ≠ 0) (hα : α ≠ 0) (hr : 0 < r) (hrR : r < R)
    (hgap : segment ℝ (τ-δ) (τ+δ) ⊆ ball c r)
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hQ : AnalyticOnNhd ℂ Q (closedBall c R \ segment ℝ (τ-δ) (τ+δ)))
    (hsq : ∀ z ∈ closedBall c R \ segment ℝ (τ-δ) (τ+δ),
      Q z^2 = (τ-δ-z)*(τ+δ-z))
    (hperiod : (∮ z in C(c,r), g z/Q z) = 0)
    (hreal : ∀ z ∈ segment ℝ (τ-δ) (τ+δ), (α*g z).im = 0) :
    ∃ z ∈ segment ℝ (τ-δ) (τ+δ), g z = 0 := by
  have hrot : (∮ z in C(c,r), (α*g z)/Q z) = 0 := by
    simp_rw [show ∀ z, (α*g z)/Q z = α*(g z/Q z) by intro z; ring]
    rw [circleIntegral.integral_const_mul,hperiod,mul_zero]
  obtain ⟨z,hz,hzero⟩ := exists_gap_zero_of_real_zero_period
    (fun z => α*g z) Q τ δ c r R hδ hr hrR hgap (analyticOnNhd_const.mul hg)
    hQ hsq hrot hreal
  exact ⟨z,hz,(mul_eq_zero.mp hzero).resolve_left hα⟩

theorem eq_zero_of_collapsed_endpointRoot_period
    (g : ℂ → ℂ) (a c : ℂ) (r : ℝ) (ha : a ∈ ball c r)
    (hg : AnalyticOnNhd ℂ g (closedBall c r))
    (hperiod : (∮ z in C(c,r), g z/endpointRoot a a z) = 0) : g a = 0 := by
  have hroot (z : ℂ) : endpointRoot a a z = a-z := by
    simp only [endpointRoot,sub_self,zero_pow (by norm_num : 2 ≠ 0),
      NLS.ZakharovShabat.normalizedStandardRoot_zeroGap,
      show (a+a)/2 = a by ring]
  have heq : (fun z => g z/endpointRoot a a z) = (fun z => (-1)*(g z/(z-a))) := by
    funext z
    rw [hroot,show a-z = -(z-a) by ring,div_neg,neg_one_mul]
  have hi := circleIntegral_div_sub_of_differentiable_on_off_countable countable_empty ha
    hg.continuousOn (fun z hz => (hg z (ball_subset_closedBall hz.1)).differentiableAt)
  rw [heq,circleIntegral.integral_const_mul,hi,neg_one_mul,neg_eq_zero] at hperiod
  exact (mul_eq_zero.mp hperiod).resolve_left (by simp [Real.pi_ne_zero])

theorem exists_segment_zero_of_endpointRoot_zero_period
    (g : ℂ → ℂ) (a b c α : ℂ) (r R : ℝ)
    (hα : α ≠ 0) (hr : 0 < r) (hrR : r < R)
    (hgap : segment ℝ a b ⊆ ball c r)
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hperiod : (∮ z in C(c,r), g z/endpointRoot a b z) = 0)
    (hreal : ∀ z ∈ segment ℝ a b, (α*g z).im = 0) :
    ∃ z ∈ segment ℝ a b, g z = 0 := by
  by_cases hab : a = b
  · subst b
    exact ⟨a,left_mem_segment ℝ _ _,eq_zero_of_collapsed_endpointRoot_period
      g a c r (hgap (left_mem_segment ℝ _ _))
      (hg.mono (closedBall_subset_closedBall hrR.le)) hperiod⟩
  let τ := (a+b)/2
  let δ := (b-a)/2
  have hl : τ-δ = a := by dsimp [τ,δ]; ring
  have hu : τ+δ = b := by dsimp [τ,δ]; ring
  have hδ : δ ≠ 0 := by
    dsimp [δ]
    exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hab)) (by norm_num)
  have hQ : AnalyticOnNhd ℂ (endpointRoot a b)
      (closedBall c R \ segment ℝ (τ-δ) (τ+δ)) := by
    rw [hl,hu]
    exact (analyticOnNhd_endpointRoot a b).mono (fun _ hz => hz.2)
  have hsq (z : ℂ) (hz : z ∈ closedBall c R \ segment ℝ (τ-δ) (τ+δ)) :
      endpointRoot a b z^2 = (τ-δ-z)*(τ+δ-z) := by
    rw [hl,hu] at hz ⊢
    rw [endpointRoot_sq a b z hz.2]
    ring
  simpa only [hl,hu] using exists_gap_zero_of_rotated_zero_period
    g (endpointRoot a b) τ δ c α r R hδ hα hr hrR (by simpa only [hl,hu] using hgap)
    hg hQ hsq hperiod (by simpa only [hl,hu] using hreal)

theorem exists_segment_zero_of_deflated_root_period
    (N U : ℂ → ℂ) (a b c α : ℂ) (r R : ℝ)
    (hα : α ≠ 0) (hr : 0 < r) (hrR : r < R)
    (hgap : segment ℝ a b ⊆ ball c r)
    (hN : AnalyticOnNhd ℂ N (closedBall c R))
    (hU : AnalyticOnNhd ℂ U (closedBall c R))
    (hUne : ∀ z ∈ closedBall c R, U z ≠ 0)
    (hperiod : (∮ z in C(c,r), N z/(endpointRoot a b z*U z)) = 0)
    (hreal : ∀ z ∈ segment ℝ a b, (α*(N z/U z)).im = 0) :
    ∃ z ∈ segment ℝ a b, N z = 0 := by
  have hg : AnalyticOnNhd ℂ (fun z => N z/U z) (closedBall c R) :=
    fun z hz => (hN z hz).div (hU z hz) (hUne z hz)
  have hp : (∮ z in C(c,r), (N z/U z)/endpointRoot a b z) = 0 := by
    have he : (fun z => (N z/U z)/endpointRoot a b z) =
        (fun z => N z/(endpointRoot a b z*U z)) := by
      funext z
      rw [div_div,mul_comm]
    rwa [he]
  obtain ⟨z,hz,hzero⟩ := exists_segment_zero_of_endpointRoot_zero_period
    (fun z => N z/U z) a b c α r R hα hr hrR hgap hg hp hreal
  exact ⟨z,hz,(div_eq_zero_iff.mp hzero).resolve_right
    (hUne z (ball_subset_closedBall (ball_subset_ball hrR.le (hgap hz))))⟩

end NLS.ComplexAnalysis
