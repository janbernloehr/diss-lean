import NLS.KdV.ClassicalHillDiscAsymptotics
import NLS.KdV.ClassicalHillHighTracePhase

/-! # Uniform normalized trace control on small high Hill discs

A single positive radius, spectral cutoff and complex source neighborhood
put the parity-normalized trace in any chosen neighborhood of one on
every complete high disc, including along all straight source paths.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem norm_hill_normalized_trace_sub_one_le
    (q : Curve ℂ) (n : ℕ) (z : ℂ) :
    ‖(-1 : ℂ)^n*classicalHillDiscriminant q (z^2)/2-1‖ ≤
      ‖classicalHillDiscriminant q (z^2)-2*cos z‖/2 +
        ‖cos (z-(Real.pi : ℂ)*n)-1‖ := by
  have he : (-1 : ℂ)^n*classicalHillDiscriminant q (z^2)/2-1 =
      (-1 : ℂ)^n*(classicalHillDiscriminant q (z^2)-2*cos z)/2 +
        (cos (z-(Real.pi : ℂ)*n)-1) := by
    have h := freeHillTrace_parity_shift n z
    linear_combination h/2
  rw [he]
  have hn : ‖(-1 : ℂ)^n*(classicalHillDiscriminant q (z^2)-2*cos z)/2‖ =
      ‖classicalHillDiscriminant q (z^2)-2*cos z‖/2 := by
    rw [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    norm_num
  exact (norm_add_le _ _).trans_eq (congrArg (fun t => t+‖cos (z-(Real.pi : ℂ)*n)-1‖) hn)

/-- The tolerance is chosen before one radius, cutoff and complex
neighborhood serving the whole high family and every source segment. -/
theorem exists_classicalHill_small_disc_normalized_trace
    (q : Curve ℂ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set (Curve ℂ),
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ∀ n : ℕ, N ≤ n →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
          ‖(-1 : ℂ)^n*classicalHillDiscriminant ((s : ℂ) • a) (z^2)/2-1‖ < delta := by
  obtain ⟨R,hR,hcos⟩ := Metric.continuousAt_iff.mp
    (continuous_cos.continuousAt : ContinuousAt cos (0 : ℂ)) (delta/2) (half_pos hdelta)
  let r : ℝ := min (Real.pi/4) (R/2)
  have hr : 0 < r := by dsimp only [r]; exact lt_min (by positivity) (half_pos hR)
  have hrpi : r ≤ Real.pi/4 := min_le_left _ _
  obtain ⟨N,V,hN,hV,hq,hd⟩ := exists_classicalHill_source_disc_trace_approximation q r hr hrpi
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
  have h := norm_hill_normalized_trace_sub_one_le ((s : ℂ) • a) n z
  linarith

end NLS.KdV
