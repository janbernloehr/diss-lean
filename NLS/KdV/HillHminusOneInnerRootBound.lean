import NLS.KdV.HillHminusOneUniformSmallTrace
import NLS.KdV.HillUniformFrequencySine
import NLS.KdV.ClassicalContourCoverage
/-! # Uniform actual root bounds on inner frequency circles

One complex H^-1 ball works before all positive contours. Radial source
segments stay in this ball, proving actual sheet coverage and root separation.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_uniform_inner_root_bound
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ δ b : ℝ, 0 < δ ∧ 0 < b ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ k : ℕ+,
        ∀ w ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
          ‖hillHminusDiscriminant q (w^2)‖ ≤ 1+2*Real.exp (Real.pi/4)) ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ k : ℕ+,
        ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) r,
          (z^2,q) ∈ hillHminusContinuationDomain ∧ b ≤ ‖hillHminusContinuedRoot (z^2,q)‖ := by
  obtain ⟨b,hb,hsin⟩ := exists_uniform_frequencyCircle_sin_lower_bound r hr
    (by linarith [Real.pi_pos])
  let M := Real.exp (Real.pi/4)
  have hM : 0 < M := Real.exp_pos _
  let ε := min 1 (b^2/(1+4*M))
  have hden : 0 < 1+4*M := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos (sq_pos_of_pos hb) hden)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hbudget : ε*(1+4*M) ≤ b^2 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨U,hU,h0U,htrace⟩ := exists_hillHminus_uniform_small_disc_trace
    (Real.pi/4) (by positivity) le_rfl ε hε
  obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp hU 0 h0U
  have hrad (q : PeriodOneHminusOne) (hq : q ∈ ball 0 δ) (k : ℕ+)
      (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) r) :
      b^2 ≤ ‖hillHminusRadicand q (z^2)‖ := by
    have hzdisc := closedBall_subset_closedBall hrpi (sphere_subset_closedBall hz)
    exact norm_radicand_lower_of_trace_close _ z ε M b hε.le hb hε1 hbudget
      (htrace q (hδU hq) k z hzdisc)
      (norm_cos_le_exp_on_free_disc _ k z hzdisc) (hsin k z hz)
  refine ⟨δ,b,hδ,hb,?_,?_⟩
  · intro q hq k w hw
    have ht := norm_add_le (hillHminusDiscriminant q (w^2)-2*cos w) (2*cos w)
    rw [sub_add_cancel,norm_mul,norm_ofNat] at ht
    have hc := norm_cos_le_exp_on_free_disc _ k w hw
    have hd := htrace q (hδU hq) k w hw
    linarith
  · intro q hq k z hz
    have hzdisc := closedBall_subset_closedBall hrpi (sphere_subset_closedBall hz)
    have ht : (z^2,q) ∈ hillHminusContinuationDomain := by
      rw [mem_hillHminusContinuationDomain_iff]
      refine ⟨sq_mem_slitPlane_of_high_closedBall k k.property z hzdisc,?_⟩
      intro s hs he
      have hsq : (s : ℂ) • q ∈ ball (0 : PeriodOneHminusOne) δ := by
        rw [mem_ball_zero_iff,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
        exact (mul_le_of_le_one_left (norm_nonneg q) hs.2).trans_lt (mem_ball_zero_iff.mp hq)
      have hl := hrad ((s : ℂ) • q) hsq k z hz
      rw [he,norm_zero] at hl
      nlinarith
    refine ⟨ht,?_⟩
    have hs := congrArg norm (hillHminusContinuedRoot_sq (z^2,q) ht)
    rw [norm_pow] at hs
    have hl := hrad q hq k z hz
    nlinarith [norm_nonneg (hillHminusContinuedRoot (z^2,q))]
end NLS.KdV
