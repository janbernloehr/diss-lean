import NLS.ComplexAnalysis.ShiftedSquareRootBounds
import NLS.KdV.ClassicalHillHighTracePhase
import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform free Hill trace control under a fixed energy translation

Parity translation reduces all high discs to a single compact disc.
Uniform continuity of the free cosine trace then transfers the small
frequency shift to a common trace-error bound.
-/
noncomputable section
set_option autoImplicit false
open Complex Set Metric NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_high_disc_free_trace_shift_small (c : ℂ) (r epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ z ∈ closedBall ((Real.pi : ℂ)*n) r,
      ‖2*cos (sqrt (z^2+c))-2*cos z‖ < epsilon := by
  have huc : UniformContinuousOn (fun z : ℂ => 2*cos z) (closedBall 0 (r+1)) :=
    (isCompact_closedBall (0 : ℂ) (r+1)).uniformContinuousOn_of_continuous
      (continuous_const.mul continuous_cos).continuousOn
  obtain ⟨delta,hdelta,hd⟩ := Metric.uniformContinuousOn_iff.mp huc epsilon hepsilon
  obtain ⟨N,hN,hsmall⟩ := exists_high_disc_sqrt_shift_small c r (min 1 delta) (lt_min zero_lt_one hdelta)
  refine ⟨N,hN,?_⟩
  intro n hn z hz
  let w := sqrt (z^2+c)
  let p : ℂ := (Real.pi : ℂ)*n
  have hclose : ‖w-z‖ < min 1 delta := (hsmall n hn z hz).2
  have hzb : ‖z-p‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hwb : ‖w-p‖ ≤ r+1 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub w z p
    have hc : ‖w-z‖ < 1 := hclose.trans_le (min_le_left _ _)
    linarith
  have hmemw : w-p ∈ closedBall (0 : ℂ) (r+1) := by
    simpa only [mem_closedBall,dist_zero_right] using hwb
  have hmemz : z-p ∈ closedBall (0 : ℂ) (r+1) := by
    simp only [mem_closedBall,dist_zero_right]
    linarith
  have hdist : dist (w-p) (z-p) < delta := by
    rw [dist_eq_norm,show (w-p)-(z-p) = w-z by ring]
    exact hclose.trans_le (min_le_right _ _)
  have hcos := hd (w-p) hmemw (z-p) hmemz hdist
  rw [dist_eq_norm] at hcos
  calc
    ‖2*cos w-2*cos z‖ = ‖(-1 : ℂ)^n*(2*cos w-2*cos z)‖ := by
      rw [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    _ = ‖2*cos (w-p)-2*cos (z-p)‖ := by
      rw [mul_sub,freeHillTrace_parity_shift,freeHillTrace_parity_shift]
    _ < epsilon := hcos


end NLS.KdV
