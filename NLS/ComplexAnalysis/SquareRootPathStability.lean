import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.IntermediateValue

/-! # Stability of a normalized square root along a path

Closeness of squares alone allows a sign change. A continuous path anchored
at the chosen root cannot cross the separating circle while its square
stays sufficiently close. This retains the original square-root branch.
-/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

/-- A continuous square-root path keeps the branch fixed at time zero.
The lower bound can be chosen uniformly over a compact parameter set. -/
theorem norm_sub_lt_of_square_path (q : ℝ → ℂ) (c : ℂ) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hc : δ ≤ ‖c‖)
    (hq : ContinuousOn q (Icc (0 : ℝ) 1)) (hzero : q 0 = c)
    (hsq : ∀ t ∈ Icc (0 : ℝ) 1, ‖q t ^ 2-c^2‖ < δ*min δ ε) :
    ‖q 1-c‖ < ε := by
  have hprod (t : ℝ) : ‖q t-c‖*‖q t+c‖ = ‖q t^2-c^2‖ := by
    rw [← norm_mul]
    congr 1
    ring
  have hsum (t : ℝ) : 2*‖c‖ ≤ ‖q t-c‖+‖q t+c‖ := by
    have he : (q t+c)-(q t-c) = 2*c := by ring
    have h := norm_sub_le (q t+c) (q t-c)
    rw [he,norm_mul,show ‖(2 : ℂ)‖ = 2 by norm_num] at h
    linarith
  have hsmall (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖q t^2-c^2‖ < ‖c‖^2 :=
    (hsq t ht).trans_le (by nlinarith [min_le_left δ ε,sq_nonneg (‖c‖-δ)])
  have hne (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖q t-c‖ ≠ ‖c‖ := by
    intro he
    have hp := hprod t
    have hs := hsum t
    have hb := hsmall t ht
    rw [he] at hp hs
    nlinarith [norm_nonneg c]
  have hlt : ‖q 1-c‖ < ‖c‖ := isPreconnected_Icc.gt_of_ne
    (hq.sub continuousOn_const).norm hne
    ⟨0,by simp,by simpa [hzero] using hδ.trans_le hc⟩ (by simp)
  have hlast := hsq 1 (by simp)
  have hupper : ‖q 1^2-c^2‖ < δ*ε :=
    hlast.trans_le (mul_le_mul_of_nonneg_left (min_le_right δ ε) hδ.le)
  have hp := hprod 1
  have hs := hsum 1
  by_contra hn
  have hge : ε ≤ ‖q 1-c‖ := le_of_not_gt hn
  nlinarith

end NLS.ComplexAnalysis
