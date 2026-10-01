import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith

/-! # A finite derivative limit of a bounded real curve is zero

A nonzero limiting derivative would give an eventual fixed slope bound.
The mean value theorem then forces growth exceeding the curve's bound.
-/

open Set Filter Topology
namespace NLS.FunctionalAnalysis

private theorem not_pos_derivative_limit_of_bounded
    (f g : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (g t) t)
    (M : ℝ) (hbound : ∀ t, ‖f t‖ ≤ M)
    (L : ℝ) (hlim : Tendsto g atTop (𝓝 L)) (hL : 0 < L) : False := by
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hbound 0)
  have hC : 0 < L/2 := by linarith
  obtain ⟨A,hA⟩ := eventually_atTop.mp
    (hlim.eventually (lt_mem_nhds (show L/2 < L by linarith)))
  let T : ℝ := A+(2*M+1)/(L/2)
  have hT : A < T := by
    dsimp [T]
    exact lt_add_of_pos_right A (div_pos (by linarith) hC)
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope f g hT
    (by exact (continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)).continuousOn)
    (fun t _ => hf t)
  have hs : (L/2)*(T-A) < f T-f A :=
    (lt_div_iff₀ (sub_pos.mpr hT)).mp (he ▸ hA c hc.1.le)
  have hprod : (L/2)*(T-A) = 2*M+1 := by
    dsimp [T]
    rw [add_sub_cancel_left,mul_div_cancel₀ _ (ne_of_gt hC)]
  have hBT := abs_le.mp (by simpa only [Real.norm_eq_abs] using hbound T)
  have hBA := abs_le.mp (by simpa only [Real.norm_eq_abs] using hbound A)
  rw [hprod] at hs
  linarith

/-- If a bounded differentiable real curve's actual derivative has a
finite limit at positive infinity, that limit is zero. -/
theorem derivative_limit_eq_zero_of_bounded
    (f g : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (g t) t)
    (M : ℝ) (hbound : ∀ t, ‖f t‖ ≤ M)
    (L : ℝ) (hlim : Tendsto g atTop (𝓝 L)) : L = 0 := by
  rcases lt_trichotomy L 0 with hneg | heq | hpos
  · exact False.elim (not_pos_derivative_limit_of_bounded
      (fun t => -f t) (fun t => -g t) (fun t => (hf t).neg) M
      (by simpa only [norm_neg] using hbound) (-L) hlim.neg (neg_pos.mpr hneg))
  · exact heq
  · exact False.elim (not_pos_derivative_limit_of_bounded f g hf M hbound L hlim hpos)

end NLS.FunctionalAnalysis
