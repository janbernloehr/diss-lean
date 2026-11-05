import NLS.KdV.HillL2DiscAsymptotics
import NLS.KdV.ClassicalHillHighTracePhase

/-! # Uniform phase and normalized-trace control for L2 Hill potentials

One complex L2 neighborhood and one high cutoff control entire frequency
discs along every straight source path. The parity-normalized trace has
positive real part and lies arbitrarily close to one on smaller discs.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

/-- A small additive trace error fixes the correct parity half-plane
on every point of a high disc, including its interior spectral zeros. -/
theorem hillL2Trace_parity_re_pos_of_error
    (q : Coeff 2) (n : ℕ) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4))
    (he : ‖hillL2Discriminant q (z^2)-2*cos z‖ ≤ (1/2 : ℝ)) :
    0 < ((-1 : ℂ)^n*hillL2Discriminant q (z^2)).re := by
  have hf := one_half_lt_re_cos_of_norm_le (z-(Real.pi : ℂ)*n)
    (by simpa only [mem_closedBall,dist_eq_norm] using hz)
  have hd : ‖(-1 : ℂ)^n*hillL2Discriminant q (z^2)-(-1 : ℂ)^n*(2*cos z)‖ ≤ (1/2 : ℝ) := by
    rw [← mul_sub,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    exact he
  have hdiff := abs_le.mp ((abs_re_le_norm _).trans hd)
  rw [freeHillTrace_parity_shift,sub_re] at hdiff
  have htwo : (2*cos (z-(Real.pi : ℂ)*n)).re = 2*(cos (z-(Real.pi : ℂ)*n)).re := by simp
  rw [htwo] at hdiff
  linarith [hdiff.1]

/-- One common complex neighborhood has the correct parity trace
half-plane on every complete high disc and every straight source path. -/
theorem exists_hillL2_source_high_trace_phase (q : Coeff 2) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ∀ n : ℕ, N ≤ n →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4),
          0 < ((-1 : ℂ)^n*hillL2Discriminant ((s : ℂ) • a) (z^2)).re := by
  obtain ⟨N,V,hN,hV,hq,hd⟩ := exists_hillL2_source_disc_trace_approximation q
    (Real.pi/4) (by positivity) le_rfl (1/2) (by norm_num)
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha s hs n hn z hz
  apply hillL2Trace_parity_re_pos_of_error _ n z hz
  exact hd a ha s hs n (by simpa only [Int.natAbs_natCast] using hn) z
    (by simpa only [Int.cast_natCast] using hz)

theorem norm_hillL2_normalized_trace_sub_one_le
    (q : Coeff 2) (n : ℕ) (z : ℂ) :
    ‖(-1 : ℂ)^n*hillL2Discriminant q (z^2)/2-1‖ ≤
      ‖hillL2Discriminant q (z^2)-2*cos z‖/2 +
        ‖cos (z-(Real.pi : ℂ)*n)-1‖ := by
  have he : (-1 : ℂ)^n*hillL2Discriminant q (z^2)/2-1 =
      (-1 : ℂ)^n*(hillL2Discriminant q (z^2)-2*cos z)/2 +
        (cos (z-(Real.pi : ℂ)*n)-1) := by
    have h := freeHillTrace_parity_shift n z
    linear_combination h/2
  rw [he]
  have hn : ‖(-1 : ℂ)^n*(hillL2Discriminant q (z^2)-2*cos z)/2‖ =
      ‖hillL2Discriminant q (z^2)-2*cos z‖/2 := by
    rw [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    norm_num
  exact (norm_add_le _ _).trans_eq (congrArg (fun t => t+‖cos (z-(Real.pi : ℂ)*n)-1‖) hn)

/-- The tolerance is chosen before one radius, cutoff and complex
neighborhood serving the whole high family and every source segment. -/
theorem exists_hillL2_small_disc_normalized_trace
    (q : Coeff 2) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Coeff 2),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ∀ n : ℕ, N ≤ n →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
          ‖(-1 : ℂ)^n*hillL2Discriminant ((s : ℂ) • a) (z^2)/2-1‖ < delta := by
  obtain ⟨R,hR,hcos⟩ := Metric.continuousAt_iff.mp
    (continuous_cos.continuousAt : ContinuousAt cos (0 : ℂ)) (delta/2) (half_pos hdelta)
  let r : ℝ := min (Real.pi/4) (R/2)
  have hr : 0 < r := by dsimp only [r]; exact lt_min (by positivity) (half_pos hR)
  have hrpi : r ≤ Real.pi/4 := min_le_left _ _
  obtain ⟨N,V,hN,hV,hq,hd⟩ := exists_hillL2_source_disc_trace_approximation q r hr hrpi
    (delta/2) (half_pos hdelta)
  refine ⟨r,N,V,hr,hrpi,hN,hV,hq,?_⟩
  intro a ha s hs n hn z hz
  have hzR : ‖z-(Real.pi : ℂ)*n‖ < R := by
    have hz' : ‖z-(Real.pi : ℂ)*n‖ ≤ r := by
      simpa only [mem_closedBall,dist_eq_norm] using hz
    have hrR : r ≤ R/2 := min_le_right _ _
    linarith
  have hfree : ‖cos (z-(Real.pi : ℂ)*n)-1‖ < delta/2 := by
    have h := hcos (by simpa only [dist_zero_right] using hzR)
    simpa only [cos_zero,dist_eq_norm] using h
  have hbound := hd a ha s hs n (by simpa only [Int.natAbs_natCast] using hn) z
    (by simpa only [Int.cast_natCast] using hz)
  have h := norm_hillL2_normalized_trace_sub_one_le ((s : ℂ) • a) n z
  linarith

end NLS.KdV
