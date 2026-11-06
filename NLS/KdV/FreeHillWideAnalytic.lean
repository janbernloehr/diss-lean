import NLS.KdV.FreeHillAnalytic
import NLS.KdV.PseudomeasureWideComparison

/-! The same total free-symbol family is analytic on every full radius-12n
strip for n≥2. Its coefficients are the actual wide complementary inverse. -/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.KdV

/-- The free denominators remain separated in a ball about every closed-strip point. -/
theorem freeHill_denominator_near_wide {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    (hz : z ∈ wideHillStrip n) {y : ℂ} (hy : y ∈ ball z ((n:ℝ)/2))
    {k : ℤ} (hk : k.natAbs ≠ n) : (n:ℝ)/2 ≤ ‖y-(freeHillValue k:ℂ)‖ := by
  have hd := wideHill_denominator_ge n hn z hz k hk
  have hdist : ‖z-y‖ < (n:ℝ)/2 := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hy
  have ht : ‖z-(freeHillValue k:ℂ)‖ ≤ ‖z-y‖+‖y-(freeHillValue k:ℂ)‖ := by
    calc
      _ = ‖(z-y)+(y-(freeHillValue k:ℂ))‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  linarith

/-- Exact agreement with the constructed reduced free Hill inverse on the closed strip. -/
theorem hillOrderTwoSymbolFamily_eq_wide_symbol (n : ℕ) (hn : 2 ≤ n) (z : ℂ)
    (hz : z ∈ wideHillStrip n) (k : ℤ) :
    hillOrderTwoSymbolFamily n z k =
      (Weight.sobolev 2 k:ℂ)*wideHillSymbol n z k := by
  apply hillOrderTwoSymbolFamily_apply_of_gap
  intro j hj
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  exact (show (1/2:ℝ) ≤ n by linarith).trans
    (wideHill_denominator_ge n hn z hz j hj)

/-- Genuine infinity-norm analyticity at every closed-strip point, including
its boundary; no coordinatewise-only analyticity is substituted. -/
theorem analyticAt_hillOrderTwoSymbolFamily_wide (n : ℕ) (hn : 2 ≤ n) (z : ℂ)
    (hz : z ∈ wideHillStrip n) : AnalyticAt ℂ (hillOrderTwoSymbolFamily n) z := by
  let U := ball z ((n:ℝ)/2)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hU : IsOpen U := isOpen_ball
  have hzU : z ∈ U := mem_ball_self (by linarith)
  have hg (y : ℂ) (hy : y ∈ U) (k : ℤ) (hk : k.natAbs ≠ n) :
      (1/2:ℝ) ≤ ‖y-(freeHillValue k:ℂ)‖ :=
    (show (1/2:ℝ) ≤ (n:ℝ)/2 by linarith).trans (freeHill_denominator_near_wide hn hz hy hk)
  have hc (k : ℤ) : AnalyticOnNhd ℂ (fun y => hillOrderTwoSymbolFamily n y k) U := by
    intro y hy
    by_cases hk : k.natAbs = n
    · apply (analyticAt_const (v := (0:ℂ))).congr
      filter_upwards [hU.mem_nhds hy] with t ht
      rw [hillOrderTwoSymbolFamily_apply_of_gap n t (hg t ht), if_pos hk, mul_zero]
    · have hne : y-(freeHillValue k:ℂ) ≠ 0 := norm_pos_iff.mp (by linarith [hg y hy k hk])
      apply ((analyticAt_const (v := (Weight.sobolev 2 k:ℂ))).mul
        ((analyticAt_id.sub analyticAt_const).inv hne)).congr
      filter_upwards [hU.mem_nhds hy] with t ht
      rw [hillOrderTwoSymbolFamily_apply_of_gap n t (hg t ht), if_neg hk]
      rfl
  have hb (y : ℂ) (hy : y ∈ U) :
      ‖hillOrderTwoSymbolFamily n y‖ ≤ 6+4*(‖z‖+(n:ℝ)/2) := by
    apply (norm_hillOrderTwoSymbolFamily_le n y (hg y hy)).trans
    have hd : ‖y-z‖ < (n:ℝ)/2 := by simpa only [U, mem_ball, dist_eq_norm] using hy
    have ht := norm_le_norm_sub_add y z
    linarith
  exact Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU hc _ hb z hzU

end NLS.KdV
