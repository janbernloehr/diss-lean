import NLS.ZakharovShabat.VerticalStrips
import Mathlib.Analysis.Complex.AbsMax

/-!
# Extending bounds across all free spectral discs

Each free circle lies outside all open free discs. The maximum-modulus
principle therefore propagates an exterior bound to the entire plane.
A bounded central region may be omitted from the exterior hypothesis.
-/

noncomputable section
open Set Complex Metric
namespace NLS.ZakharovShabat

theorem freeSphere_separated {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (n : ℤ) {z : ℂ} (hz : z ∈ sphere ((Real.pi : ℂ)*n) r) (m : ℤ) :
    r ≤ ‖z-(Real.pi : ℂ)*m‖ := by
  have h := verticalStrip_denominator_lower (m := m) hr hrπ (sphere_subset_verticalStrip n hrπ hz)
  have ha := mul_nonneg hr.le (abs_nonneg (((m-n : ℤ) : ℝ)))
  nlinarith

/-- An entire function bounded outside every free disc obeys that same bound everywhere. -/
theorem norm_entire_le_of_bound_off_freeDiscs {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (B : ℝ)
    (hb : ∀ z : ℂ, (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) → ‖f z‖ ≤ B) (z : ℂ) :
    ‖f z‖ ≤ B := by
  classical
  by_cases hz : ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖
  · exact hb z hz
  · push Not at hz
    obtain ⟨n, hn⟩ := hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      (isBounded_ball (x := (Real.pi : ℂ)*n) (r := r)) hf.diffContOnCl
    · intro w hw
      rw [frontier_ball _ (ne_of_gt hr)] at hw
      exact hb w (freeSphere_separated hr hrπ n hw)
    · exact subset_closure (by simpa only [mem_ball, dist_eq_norm] using hn)

/-- A bound only at large exterior spectral parameters still bounds the whole entire function. -/
theorem isBounded_entire_of_bound_off_freeDiscs {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) (R B : ℝ)
    (hb : ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) → ‖f z‖ ≤ B) :
    Bornology.IsBounded (range f) := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℂ) R).image hf.continuous).isBounded.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max B C, ?_⟩
  rintro w ⟨z, rfl⟩
  apply norm_entire_le_of_bound_off_freeDiscs hf hr hrπ (max B C) _ z
  intro u hu
  by_cases hR : ‖u‖ ≤ R
  · exact (hC (f u) ⟨u, by simpa only [mem_closedBall, dist_zero_right] using hR, rfl⟩).trans
      (le_max_right _ _)
  · exact (hb u (le_of_not_ge hR) hu).trans (le_max_left _ _)

end NLS.ZakharovShabat
