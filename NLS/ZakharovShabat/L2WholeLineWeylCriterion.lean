import NLS.ZakharovShabat.L2WholeLineNonrealResolvent

/-! # Approximate eigenvectors for the original whole-line spectrum

The criterion uses the independently defined bounded inverse of the actual
physical pencil. It does not define the spectrum from Floquet multipliers.
-/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace NLS.ZakharovShabat

/-- A bounded resolvent bounds the input norm by the original pencil norm. -/
theorem wholeLinePencil_norm_bound_of_mem_resolvent (u : IntervalPairL2) (z : ℂ)
    (hz : z ∈ wholeLineResolventSet u) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (wholeLineMinimalOperator u).closure.domain,
      ‖(f : WholeLineL2)‖ ≤ C * ‖wholeLinePencil u z f‖ := by
  obtain ⟨R,_,hR⟩ := hz
  refine ⟨‖R‖+1,by positivity,fun f => ?_⟩
  have hb := R.le_opNorm (wholeLinePencil u z f)
  rw [hR] at hb
  change ‖(f : WholeLineL2)‖ ≤ ‖R‖ * ‖wholeLinePencil u z f‖ at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))

/-- Normalized approximate eigenvectors force membership in the actual
whole-line operator spectrum. No weak-convergence premise is needed. -/
theorem mem_wholeLineSpectrum_of_approximate_eigenvectors
    (u : IntervalPairL2) (z : ℂ)
    (f : ℕ → (wholeLineMinimalOperator u).closure.domain)
    (hn : ∀ n, ‖(f n : WholeLineL2)‖ = 1)
    (hr : Tendsto (fun n => wholeLinePencil u z (f n)) atTop (𝓝 0)) :
    z ∈ wholeLineSpectrum u := by
  intro hz
  obtain ⟨C,hC,hbound⟩ := wholeLinePencil_norm_bound_of_mem_resolvent u z hz
  have hl : Tendsto (fun n => C * ‖wholeLinePencil u z (f n)‖) atTop (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using hr.norm.const_mul C
  obtain ⟨n,hnlt⟩ := (hl.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).exists
  have hb := hbound (f n)
  rw [hn] at hb
  linarith

/-- The equivalent epsilon form avoids choosing a particular sequence. -/
theorem mem_wholeLineSpectrum_of_arbitrarily_small_residual
    (u : IntervalPairL2) (z : ℂ)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ f : (wholeLineMinimalOperator u).closure.domain,
      ‖(f : WholeLineL2)‖ = 1 ∧ ‖wholeLinePencil u z f‖ < ε) :
    z ∈ wholeLineSpectrum u := by
  intro hz
  obtain ⟨C,hC,hbound⟩ := wholeLinePencil_norm_bound_of_mem_resolvent u z hz
  obtain ⟨f,hn,hr⟩ := hf (1/C) (div_pos zero_lt_one hC)
  have hb := hbound f
  rw [hn] at hb
  have hsmall := mul_lt_mul_of_pos_left hr hC
  rw [mul_one_div_cancel (ne_of_gt hC)] at hsmall
  linarith

end NLS.ZakharovShabat
