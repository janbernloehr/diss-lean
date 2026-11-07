import NLS.KdV.FreeHillRegularity
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! # Banach analytic free Hill symbols on neighborhoods of the closed strips

The total family is identified with the actual reduced reciprocal symbol at
every point of the corrected closed strip. Analyticity is in the weighted
infinity norm and includes boundary points of the strip.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.KdV

/-- The free denominators remain separated in a ball about every closed-strip point. -/
theorem freeHill_denominator_near {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ reducedHillStrip n) {y : ℂ} (hy : y ∈ ball z ((n:ℝ)/2))
    {k : ℤ} (hk : k.natAbs ≠ n) : (n:ℝ)/2 ≤ ‖y-(freeHillValue k:ℂ)‖ := by
  have hd := freeHill_denominator_ge_index hn hz hk
  have hdist : ‖z-y‖ < (n:ℝ)/2 := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hy
  have ht : ‖z-(freeHillValue k:ℂ)‖ ≤ ‖z-y‖+‖y-(freeHillValue k:ℂ)‖ := by
    calc
      _ = ‖(z-y)+(y-(freeHillValue k:ℂ))‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  linarith

/-- A uniform half-unit denominator gap controls the two-derivative symbol. -/
theorem hillOrderTwoRaw_bound (n : ℕ) (y : ℂ)
    (hgap : ∀ k : ℤ, k.natAbs ≠ n → (1/2:ℝ) ≤ ‖y-(freeHillValue k:ℂ)‖) (k : ℤ) :
    ‖(Weight.sobolev 2 k:ℂ)*(if k.natAbs = n then 0 else (y-(freeHillValue k:ℂ))⁻¹)‖ ≤
      6+4*‖y‖ := by
  by_cases hk : k.natAbs = n
  · simp only [if_pos hk, mul_zero, norm_zero]
    positivity
  · have hd := hgap k hk
    have hv : 0 ≤ freeHillValue k := by unfold freeHillValue; positivity
    have ht : freeHillValue k ≤ ‖y‖+‖y-(freeHillValue k:ℂ)‖ := by
      calc
        _ = ‖(freeHillValue k:ℂ)‖ := by simp [abs_of_nonneg hv]
        _ = ‖y-(y-(freeHillValue k:ℂ))‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    rw [if_neg hk, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev 2).positive k), norm_inv, ← div_eq_mul_inv]
    apply (div_le_iff₀ (by linarith : 0 < ‖y-(freeHillValue k:ℂ)‖)).mpr
    have hw := sobolev_two_le_freeHillValue k
    nlinarith [mul_nonneg (norm_nonneg y) (sub_nonneg.mpr hd)]

/-- A proof-independent total family of normalized reciprocal coefficients. -/
def hillOrderTwoSymbolFamily (n : ℕ) (z : ℂ) : Coeff ⊤ :=
  Coeff.ofFunctionOrZero ⊤ (fun k => (Weight.sobolev 2 k:ℂ)*
    (if k.natAbs = n then 0 else (z-(freeHillValue k:ℂ))⁻¹))

/-- Wherever the denominator gap is known, every actual scalar coordinate is recovered. -/
theorem hillOrderTwoSymbolFamily_apply_of_gap (n : ℕ) (z : ℂ)
    (hgap : ∀ k : ℤ, k.natAbs ≠ n → (1/2:ℝ) ≤ ‖z-(freeHillValue k:ℂ)‖) (k : ℤ) :
    hillOrderTwoSymbolFamily n z k = (Weight.sobolev 2 k:ℂ)*
      (if k.natAbs = n then 0 else (z-(freeHillValue k:ℂ))⁻¹) := by
  apply Coeff.ofFunctionOrZero_apply_of_mem
  exact memℓp_infty ⟨6+4*‖z‖,by
    rintro _ ⟨j,rfl⟩
    exact hillOrderTwoRaw_bound n z hgap j⟩

/-- Local operator control of the two-derivative free family. -/
theorem norm_hillOrderTwoSymbolFamily_le (n : ℕ) (z : ℂ)
    (hgap : ∀ k : ℤ, k.natAbs ≠ n → (1/2:ℝ) ≤ ‖z-(freeHillValue k:ℂ)‖) :
    ‖hillOrderTwoSymbolFamily n z‖ ≤ 6+4*‖z‖ := by
  apply lp.norm_le_of_forall_le (by positivity)
  intro k
  rw [hillOrderTwoSymbolFamily_apply_of_gap n z hgap]
  exact hillOrderTwoRaw_bound n z hgap k

/-- Exact agreement with the constructed reduced free Hill inverse on the closed strip. -/
theorem hillOrderTwoSymbolFamily_eq_symbol (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    hillOrderTwoSymbolFamily n z k =
      (Weight.sobolev 2 k:ℂ)*reducedHillSymbol n hn z hz k := by
  apply hillOrderTwoSymbolFamily_apply_of_gap
  intro j hj
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  exact (show (1/2:ℝ) ≤ n by linarith).trans
    (freeHill_denominator_ge_index hn hz hj)

/-- Genuine infinity-norm analyticity at every closed-strip point, including
its boundary; no coordinatewise-only analyticity is substituted. -/
theorem analyticAt_hillOrderTwoSymbolFamily (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) : AnalyticAt ℂ (hillOrderTwoSymbolFamily n) z := by
  let U := ball z ((n:ℝ)/2)
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hU : IsOpen U := isOpen_ball
  have hzU : z ∈ U := mem_ball_self (by linarith)
  have hg (y : ℂ) (hy : y ∈ U) (k : ℤ) (hk : k.natAbs ≠ n) :
      (1/2:ℝ) ≤ ‖y-(freeHillValue k:ℂ)‖ :=
    (show (1/2:ℝ) ≤ (n:ℝ)/2 by linarith).trans (freeHill_denominator_near hn hz hy hk)
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
