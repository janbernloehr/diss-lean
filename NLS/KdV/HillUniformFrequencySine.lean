import NLS.KdV.FreeContourUniformLowerBound
import NLS.ZakharovShabat.SourceSection8SineEstimates
/-! # Uniform sine separation and stable Hill radicands

Compactness of one frequency circle gives a lower bound independent of its
positive center. Explicit trace perturbation bounds preserve radicand separation.
-/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
namespace NLS.KdV

theorem exists_uniform_frequencyCircle_sin_lower_bound (r : ℝ) (hr : 0 < r) (hrpi : r < Real.pi) :
    ∃ b : ℝ, 0 < b ∧ ∀ k : ℕ+, ∀ z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) r, b ≤ ‖sin z‖ := by
  have hne : (sphere (0 : ℂ) r).Nonempty := by
    refine ⟨(r : ℂ),?_⟩
    simp only [mem_sphere,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  obtain ⟨w,hw,hmin⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMinOn hne
    Complex.continuous_sin.norm.continuousOn
  have hsw : sin w ≠ 0 := by
    intro hs
    have he := free_derivative_zero_eq_center hrpi 0
      (by simpa only [Int.cast_zero,mul_zero] using sphere_subset_closedBall hw) (by rw [hs,mul_zero])
    have hn := mem_sphere_iff_norm.mp hw
    simp only [Int.cast_zero,mul_zero] at he
    rw [he,sub_zero,norm_zero] at hn
    linarith
  refine ⟨‖sin w‖,norm_pos_iff.mpr hsw,?_⟩
  intro k z hz
  rw [← norm_sin_sub_free_center (k : ℕ) z]
  apply hmin
  simpa only [mem_sphere,dist_zero_right] using mem_sphere_iff_norm.mp hz

theorem norm_cos_le_exp_on_free_disc (r : ℝ) (k : ℕ+) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) r) : ‖cos z‖ ≤ Real.exp r := by
  have hi : |z.im| ≤ r := by
    have ht := (abs_im_le_norm (z-(Real.pi : ℂ)*(k : ℕ))).trans (mem_closedBall_iff_norm.mp hz)
    simpa only [sub_im,mul_im,ofReal_im,natCast_im,mul_zero,zero_mul,add_zero,sub_zero] using ht
  exact (section8_norm_cos_le_exp_abs_im z).trans (Real.exp_le_exp.mpr hi)

theorem norm_radicand_sub_free_le_of_trace_close (D z : ℂ) (ε M : ℝ)
    (hε : 0 ≤ ε) (hclose : ‖D-2*cos z‖ ≤ ε) (hcos : ‖cos z‖ ≤ M) :
    ‖(D^2-4)-((2*cos z)^2-4)‖ ≤ ε*(ε+4*M) := by
  have hsum : ‖D+2*cos z‖ ≤ ε+4*M := by
    have ht := norm_add_le (D-2*cos z) (4*cos z)
    rw [show D-2*cos z+4*cos z=D+2*cos z by ring,norm_mul,norm_ofNat] at ht
    linarith
  rw [show (D^2-4)-((2*cos z)^2-4)=(D-2*cos z)*(D+2*cos z) by ring,norm_mul]
  exact mul_le_mul hclose hsum (norm_nonneg _) hε

theorem norm_radicand_lower_of_trace_close (D z : ℂ) (ε M b : ℝ)
    (hε : 0 ≤ ε) (hb : 0 < b) (hε1 : ε ≤ 1)
    (hbudget : ε*(1+4*M) ≤ b^2) (hclose : ‖D-2*cos z‖ ≤ ε)
    (hcos : ‖cos z‖ ≤ M) (hsin : b ≤ ‖sin z‖) : b^2 ≤ ‖D^2-4‖ := by
  have hdiff := norm_radicand_sub_free_le_of_trace_close D z ε M hε hclose hcos
  have hfree : ‖(2*cos z)^2-4‖ = 4*‖sin z‖^2 := by
    have he : (2*cos z)^2-4 = -4*(sin z)^2 := by
      linear_combination 4*(sin_sq_add_cos_sq z)
    rw [he,norm_mul,norm_neg,norm_ofNat,norm_pow]
  have ht := norm_sub_norm_le ((2*cos z)^2-4) (D^2-4)
  rw [norm_sub_rev ((2*cos z)^2-4) (D^2-4),hfree] at ht
  have hs := mul_self_le_mul_self hb.le hsin
  have he := mul_le_mul_of_nonneg_left (show ε+4*M ≤ 1+4*M by linarith) hε
  nlinarith
end NLS.KdV
