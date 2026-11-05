import NLS.KdV.HillUniformFrequencySine
import NLS.KdV.HillHminusOneUniformSmallTrace
import NLS.KdV.ClassicalContourCoverage
/-! # Uniform actual source-root bounds on complete positive frequency annuli

A single radial complex rough-source ball covers every closed annulus,
including the finite head. Compact free sine separation gives a uniform
positive lower bound for the actual root, not only for one chosen circle.
-/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem exists_uniform_frequencyAnnulus_sin_lower_bound
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) (hRpi : R < Real.pi) :
    ∃ b : ℝ, 0 < b ∧ ∀ k : ℕ+, ∀ z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) R,
      r ≤ ‖z-(Real.pi : ℂ)*(k : ℕ)‖ → b ≤ ‖sin z‖ := by
  let K : Set ℂ := closedBall 0 R \ ball 0 r
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) R).diff isOpen_ball
  have hne : K.Nonempty := by
    refine ⟨(r : ℂ),?_,?_⟩
    · simpa only [mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hrR
    · simp only [mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,lt_self_iff_false,not_false_eq_true]
  obtain ⟨w,hw,hmin⟩ := hK.exists_isMinOn hne Complex.continuous_sin.norm.continuousOn
  have hsw : sin w ≠ 0 := by
    intro hs
    have he := free_derivative_zero_eq_center hRpi 0
      (by simpa only [Int.cast_zero,mul_zero] using hw.1) (by rw [hs,mul_zero])
    have hn : r ≤ ‖w‖ := by
      have hn := hw.2
      simpa only [mem_ball,dist_zero_right,not_lt] using hn
    simp only [Int.cast_zero,mul_zero] at he
    rw [he,norm_zero] at hn
    linarith
  refine ⟨‖sin w‖,norm_pos_iff.mpr hsw,?_⟩
  intro k z hz hfar
  rw [← norm_sin_sub_free_center (k : ℕ) z]
  apply hmin
  constructor
  · simpa only [mem_closedBall,dist_zero_right] using mem_closedBall_iff_norm.mp hz
  · simpa only [mem_ball,dist_zero_right,not_lt] using hfar

theorem norm_hillHminusContinuedRoot_le_of_trace_bound (t : ℂ × PeriodOneHminusOne)
    (ht : t ∈ hillHminusContinuationDomain) (M : ℝ) (hM : 0 ≤ M)
    (htrace : ‖hillHminusDiscriminant t.2 t.1‖ ≤ M) : ‖hillHminusContinuedRoot t‖ ≤ M+2 := by
  have hs := congrArg norm (hillHminusContinuedRoot_sq t ht)
  rw [norm_pow] at hs
  have hr : ‖hillHminusRadicand t.2 t.1‖ ≤ ‖hillHminusDiscriminant t.2 t.1‖^2+4 := by
    exact (norm_sub_le _ _).trans_eq (by rw [norm_pow,norm_ofNat])
  have hm := mul_self_le_mul_self (norm_nonneg (hillHminusDiscriminant t.2 t.1)) htrace
  nlinarith [norm_nonneg (hillHminusContinuedRoot t)]

theorem exists_hillHminus_uniform_annular_root_bound
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ δ b : ℝ, 0 < δ ∧ 0 < b ∧
      (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ k : ℕ+,
        ∀ w ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
          ‖hillHminusDiscriminant q (w^2)‖ ≤ 1+2*Real.exp (Real.pi/4)) ∧
      ∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ k : ℕ+,
        ∀ z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4),
          r ≤ ‖z-(Real.pi : ℂ)*(k : ℕ)‖ →
          (z^2,q) ∈ hillHminusContinuationDomain ∧ b ≤ ‖hillHminusContinuedRoot (z^2,q)‖ := by
  obtain ⟨b,hb,hsin⟩ := exists_uniform_frequencyAnnulus_sin_lower_bound r (Real.pi/4) hr hrpi
    (by linarith [Real.pi_pos])
  let M := Real.exp (Real.pi/4)
  have hM : 0 < M := Real.exp_pos _
  let ε := min 1 (b^2/(1+4*M))
  have hden : 0 < 1+4*M := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos (sq_pos_of_pos hb) hden)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hbudget : ε*(1+4*M) ≤ b^2 := (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨U,hU,h0U,htrace⟩ := exists_hillHminus_uniform_small_disc_trace
    (Real.pi/4) (by positivity) le_rfl ε hε
  obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp hU 0 h0U
  have hrad (q : PeriodOneHminusOne) (hq : q ∈ ball 0 δ) (k : ℕ+)
      (z : ℂ) (hz : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4))
      (hfar : r ≤ ‖z-(Real.pi : ℂ)*(k : ℕ)‖) : b^2 ≤ ‖hillHminusRadicand q (z^2)‖ := by
    exact norm_radicand_lower_of_trace_close _ z ε M b hε.le hb hε1 hbudget
      (htrace q (hδU hq) k z hz) (norm_cos_le_exp_on_free_disc _ k z hz) (hsin k z hz hfar)
  refine ⟨δ,b,hδ,hb,?_,?_⟩
  · intro q hq k w hw
    have ht := norm_add_le (hillHminusDiscriminant q (w^2)-2*cos w) (2*cos w)
    rw [sub_add_cancel,norm_mul,norm_ofNat] at ht
    have hc := norm_cos_le_exp_on_free_disc _ k w hw
    have hd := htrace q (hδU hq) k w hw
    linarith
  · intro q hq k z hz hfar
    have ht : (z^2,q) ∈ hillHminusContinuationDomain := by
      rw [mem_hillHminusContinuationDomain_iff]
      refine ⟨sq_mem_slitPlane_of_high_closedBall k k.property z hz,?_⟩
      intro s hs he
      have hsq : (s : ℂ) • q ∈ ball (0 : PeriodOneHminusOne) δ := by
        rw [mem_ball_zero_iff,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1]
        exact (mul_le_of_le_one_left (norm_nonneg q) hs.2).trans_lt (mem_ball_zero_iff.mp hq)
      have hl := hrad ((s : ℂ) • q) hsq k z hz hfar
      rw [he,norm_zero] at hl
      nlinarith
    refine ⟨ht,?_⟩
    have hs := congrArg norm (hillHminusContinuedRoot_sq (z^2,q) ht)
    rw [norm_pow] at hs
    have hl := hrad q hq k z hz hfar
    nlinarith [norm_nonneg (hillHminusContinuedRoot (z^2,q))]
end NLS.KdV
