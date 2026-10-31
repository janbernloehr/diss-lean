import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-! # Convergence under a positive moving majorant in Appendix F -/
noncomputable section
open MeasureTheory Filter Topology
namespace NLS.ComplexAnalysis

/-- Dividing by the majorant clipped below at one gives a fixed bound. -/
theorem appendixF_normalized_majorant_bound (C g : ℝ) (hC : 0 ≤ C) (f : ℂ)
    (hf : ‖f‖ ≤ C*g) : ‖(max 1 g)⁻¹ • f‖ ≤ C := by
  have hb : 0 < max 1 g := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hfb : ‖f‖ ≤ C*max 1 g := hf.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hC)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
  calc
    (max 1 g)⁻¹*‖f‖ ≤ (max 1 g)⁻¹*(C*max 1 g) :=
      mul_le_mul_of_nonneg_left hfb (inv_nonneg.mpr hb.le)
    _ = C := by field_simp

/-- The normalization error is controlled by the L1 error of the moving majorant. -/
theorem appendixF_normalized_majorant_error (C g : ℝ) (hC : 0 ≤ C) (f : ℂ)
    (hf : ‖f‖ ≤ C*g) : ‖f-(max 1 g)⁻¹ • f‖ ≤ C*|g-1| := by
  by_cases hg : g ≤ 1
  · rw [max_eq_left hg]
    simp only [inv_one, one_smul, sub_self, norm_zero]
    exact mul_nonneg hC (abs_nonneg _)
  · have hg1 : 1 < g := lt_of_not_ge hg
    have hg0 : 0 < g := lt_trans (by norm_num) hg1
    have hinv : 0 ≤ 1-g⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hg1.le)
    rw [max_eq_right hg1.le]
    have he : f-g⁻¹ • f = (1-g⁻¹) • f := by module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]
    calc
      (1-g⁻¹)*‖f‖ ≤ (1-g⁻¹)*(C*g) := mul_le_mul_of_nonneg_left hf hinv
      _ = C*|g-1| := by
        rw [abs_of_pos (sub_pos.mpr hg1)]
        field_simp

/-- For a finite measure, pointwise convergence under majorants approaching one in L1
implies convergence of the complex integrals. The moving singularity is allowed. -/
theorem appendixF_tendsto_integral_moving_majorant {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (F : ℕ → α → ℂ) (f : α → ℂ)
    (g : ℕ → α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hg : ∀ n, Integrable (g n) μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ C*g n x)
    (hFlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hglim : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 1))
    (hgL1 : Tendsto (fun n => ∫ x, |g n x-1| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  let B : ℕ → α → ℂ := fun n x => (max 1 (g n x))⁻¹ • F n x
  have hBm : ∀ n, AEStronglyMeasurable (B n) μ := by
    intro n
    exact ((aemeasurable_const.max (hg n).aemeasurable).inv.aestronglyMeasurable).smul (hF n)
  have hBb : ∀ n, ∀ᵐ x ∂μ, ‖B n x‖ ≤ C := by
    intro n
    filter_upwards [hbound n] with x hx
    exact appendixF_normalized_majorant_bound C (g n x) hC (F n x) hx
  have hBi : ∀ n, Integrable (B n) μ := fun n => (integrable_const C).mono' (hBm n) (hBb n)
  have hFi : ∀ n, Integrable (F n) μ := fun n => ((hg n).const_mul C).mono' (hF n) (hbound n)
  have hBl : ∀ᵐ x ∂μ, Tendsto (fun n => B n x) atTop (𝓝 (f x)) := by
    filter_upwards [hFlim, hglim] with x hfx hgx
    have hi : Tendsto (fun n => (max 1 (g n x))⁻¹) atTop (𝓝 (1:ℝ)) := by
      simpa using (tendsto_const_nhds.max hgx).inv₀ (by norm_num : max (1:ℝ) 1 ≠ 0)
    simpa only [one_smul] using hi.smul hfx
  have hBI := tendsto_integral_of_dominated_convergence (fun _ => C) hBm
    (integrable_const C) hBb hBl
  have herror : ∀ n, ‖∫ x, (F n x-B n x) ∂μ‖ ≤ C*(∫ x, |g n x-1| ∂μ) := by
    intro n
    have hm := ((hg n).sub (integrable_const 1)).abs.const_mul C
    calc
      ‖∫ x, (F n x-B n x) ∂μ‖ ≤ ∫ x, C*|g n x-1| ∂μ := by
        apply norm_integral_le_of_norm_le hm
        filter_upwards [hbound n] with x hx
        exact appendixF_normalized_majorant_error C (g n x) hC (F n x) hx
      _ = C*(∫ x, |g n x-1| ∂μ) := integral_const_mul C _
  have he : Tendsto (fun n => ∫ x, (F n x-B n x) ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero_norm herror
    simpa only [mul_zero] using tendsto_const_nhds.mul hgL1
  convert hBI.add he using 1
  · ext n
    rw [integral_sub (hFi n) (hBi n)]
    abel
  · simp only [add_zero]

end NLS.ComplexAnalysis
