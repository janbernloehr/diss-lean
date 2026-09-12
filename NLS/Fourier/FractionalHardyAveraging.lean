import NLS.Fourier.FractionalHardyKernel

/-!
# Tonelli identity for the fractional Hardy averaging operator

The triangular averaging kernel is measurable and its weighted mass can be
computed exactly, even for nonintegrable nonnegative input. Restricting to a
truncated interval gives the contraction estimate used in the Hardy proof.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The triangle `x<y<2x`, written as the annulus `y/2<x<y` in the first variable. -/
def hardyAveragingKernel (s x y : ℝ) : ℝ≥0∞ :=
  (Ioo (y / 2) y).indicator (fun x => ENNReal.ofReal (x ^ (-(1 + 2 * s)))) x

@[simp] theorem hardyAveragingKernel_of_mem (s : ℝ) {x y : ℝ} (hxy : x < y) (hy : y < 2 * x) :
    hardyAveragingKernel s x y = ENNReal.ofReal (x ^ (-(1 + 2 * s))) := by
  apply indicator_of_mem
  exact ⟨by linarith, hxy⟩

/-- The joint kernel is measurable, allowing genuine Tonelli interchange. -/
theorem measurable_hardyAveragingKernel (s : ℝ) :
    Measurable (fun p : ℝ × ℝ => hardyAveragingKernel s p.1 p.2) := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.2 / 2 < p.1 ∧ p.1 < p.2} :=
    (measurableSet_lt (by fun_prop) measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have h := (show Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-(1 + 2 * s)))) by
    fun_prop).indicator hm
  exact h

/-- Integrating the first variable gives the exact fractional boundary weight multiplier. -/
theorem lintegral_hardyAveragingKernel {s y : ℝ} (hs : 0 < s) (hy : 0 < y) :
    (∫⁻ x : ℝ, hardyAveragingKernel s x y) =
      ENNReal.ofReal (hardyAveragingConstant s) * ENNReal.ofReal (y ^ (-2 * s)) := by
  simp only [hardyAveragingKernel]
  rw [lintegral_indicator measurableSet_Ioo, lintegral_hardy_annulus hs hy,
    ENNReal.ofReal_mul (hardyAveragingConstant_pos hs).le]

/-- The averaging triangle is empty for nonpositive second coordinate. -/
theorem hardyAveragingKernel_of_nonpos (s : ℝ) {y : ℝ} (hy : y ≤ 0) (x : ℝ) :
    hardyAveragingKernel s x y = 0 := by
  apply indicator_of_notMem
  intro hx
  linarith [hx.1, hx.2]

/-- Exact Tonelli averaging identity for arbitrary nonnegative measurable data. -/
theorem lintegral_hardyAveraging {s : ℝ} (hs : 0 < s) (L : ℝ)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x : ℝ, ∫⁻ y : ℝ in Ioo 0 L, hardyAveragingKernel s x y * g y) =
      ENNReal.ofReal (hardyAveragingConstant s) *
        ∫⁻ y : ℝ in Ioo 0 L, ENNReal.ofReal (y ^ (-2 * s)) * g y := by
  have hm : Measurable (Function.uncurry (fun x y : ℝ => hardyAveragingKernel s x y * g y)) :=
    (measurable_hardyAveragingKernel s).mul (hg.comp measurable_snd)
  rw [lintegral_lintegral_swap hm.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro y hy
  dsimp only
  have hk : Measurable (fun x => hardyAveragingKernel s x y) :=
    (measurable_hardyAveragingKernel s).comp (measurable_id.prodMk measurable_const)
  rw [lintegral_mul_const'' _ hk.aemeasurable,
    lintegral_hardyAveragingKernel hs hy.1, mul_assoc]

/-- The triangle over `δ<x<L/2` stays inside `δ<y<L`. -/
theorem hardy_triangle_mem_interval {δ L x y : ℝ} (hx : x ∈ Ioo δ (L / 2))
    (hy : y ∈ Ioo x (2 * x)) : y ∈ Ioo δ L := by
  exact ⟨hx.1.trans hy.1, by linarith [hy.2, hx.2]⟩

/-- Averaging on a truncated interval has the exact uniform contraction bound. -/
theorem lintegral_hardyAveraging_truncated_le {s δ L : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x : ℝ in Ioo δ (L / 2), ∫⁻ y : ℝ in Ioo x (2 * x),
      ENNReal.ofReal (x ^ (-(1 + 2 * s))) * g y) ≤
      ENNReal.ofReal (hardyAveragingConstant s) *
        ∫⁻ y : ℝ in Ioo δ L, ENNReal.ofReal (y ^ (-2 * s)) * g y := by
  have hm : Measurable (Function.uncurry (fun x y : ℝ => hardyAveragingKernel s x y * g y)) :=
    (measurable_hardyAveragingKernel s).mul (hg.comp measurable_snd)
  calc
    _ ≤ ∫⁻ x : ℝ in Ioo δ (L / 2), ∫⁻ y : ℝ in Ioo δ L, hardyAveragingKernel s x y * g y := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro x hx
      calc
        _ = ∫⁻ y : ℝ in Ioo x (2 * x), hardyAveragingKernel s x y * g y := by
          apply setLIntegral_congr_fun measurableSet_Ioo
          intro y hy
          dsimp only
          rw [hardyAveragingKernel_of_mem s hy.1 hy.2]
        _ ≤ _ := lintegral_mono_set (fun y hy => hardy_triangle_mem_interval hx hy)
    _ ≤ ∫⁻ x : ℝ, ∫⁻ y : ℝ in Ioo δ L, hardyAveragingKernel s x y * g y :=
      setLIntegral_le_lintegral _ _
    _ = _ := by
      rw [lintegral_lintegral_swap hm.aemeasurable,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro y hy
      dsimp only
      have hk : Measurable (fun x => hardyAveragingKernel s x y) :=
        (measurable_hardyAveragingKernel s).comp (measurable_id.prodMk measurable_const)
      rw [lintegral_mul_const'' _ hk.aemeasurable,
        lintegral_hardyAveragingKernel hs (hδ.trans_lt hy.1), mul_assoc]

/-- The averaging kernel is dominated everywhere by the intrinsic difference kernel. -/
theorem hardyAveragingKernel_le_distance {s : ℝ} (hs : 0 ≤ s) (x y : ℝ) :
    hardyAveragingKernel s x y ≤ fractionalDistanceKernel s x y := by
  by_cases h : x ∈ Ioo (y / 2) y
  · rw [hardyAveragingKernel, indicator_of_mem h]
    exact hardy_triangle_kernel_le hs h.2 (by linarith [h.1])
  · rw [hardyAveragingKernel, indicator_of_notMem h]
    exact zero_le

/-- Viewed in the second variable, the averaging row is constant on `x<y<2x`. -/
theorem hardyAveragingKernel_row (s x : ℝ) :
    hardyAveragingKernel s x =
      (Ioo x (2 * x)).indicator (fun _ => ENNReal.ofReal (x ^ (-(1 + 2 * s)))) := by
  funext y
  have h : x ∈ Ioo (y / 2) y ↔ y ∈ Ioo x (2 * x) := by
    constructor <;> intro h <;> exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  simp only [hardyAveragingKernel, indicator_apply, h]

/-- Averaging the same value in the row recovers exactly its left boundary weight. -/
theorem lintegral_hardyAveragingKernel_row (s : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫⁻ y : ℝ, hardyAveragingKernel s x y) = ENNReal.ofReal (x ^ (-2 * s)) := by
  rw [hardyAveragingKernel_row, lintegral_indicator measurableSet_Ioo]
  simp only [setLIntegral_const, Real.volume_Ioo, show 2 * x - x = x by ring]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hx.le _)]
  congr 1
  calc
    x ^ (-(1 + 2 * s)) * x = x ^ (-(1 + 2 * s)) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = x ^ (-(1 + 2 * s) + 1) := (Real.rpow_add hx _ _).symm
    _ = x ^ (-2 * s) := by congr 1; ring

/-- The difference part of triangular averaging is bounded by the intrinsic interval energy. -/
theorem hardyAveraging_difference_le {s δ L : ℝ} (hs : 0 ≤ s) (hδ : 0 ≤ δ) (f : ℝ → ℂ) :
    (∫⁻ x : ℝ in Ioo δ (L / 2), ∫⁻ y : ℝ in Ioo δ L,
      hardyAveragingKernel s x y * ENNReal.ofReal (‖f x - f y‖ ^ 2)) ≤ fractionalIntervalEnergy s L f := by
  calc
    _ ≤ ∫⁻ x : ℝ in Ioo δ (L / 2), ∫⁻ y : ℝ in Ioo δ L,
        ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalDistanceKernel s x y := by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro y
      simpa only [mul_comm] using mul_le_mul' (hardyAveragingKernel_le_distance hs x y) le_rfl
    _ ≤ _ := by
      apply (lintegral_mono_set (show Ioo δ (L / 2) ⊆ Ioo 0 L from ?_)).trans
      · apply lintegral_mono
        intro x
        exact lintegral_mono_set (Ioo_subset_Ioo hδ le_rfl)
      · intro x hx
        exact ⟨hδ.trans_lt hx.1, by linarith [hx.2, hx.1]⟩

/-- Restricting the first variable can only reduce the exact Tonelli weighted mass. -/
theorem lintegral_hardyAveraging_restrict_le {s δ L : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ)
    (S : Set ℝ) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ x : ℝ in S, ∫⁻ y : ℝ in Ioo δ L, hardyAveragingKernel s x y * g y) ≤
      ENNReal.ofReal (hardyAveragingConstant s) *
        ∫⁻ y : ℝ in Ioo δ L, ENNReal.ofReal (y ^ (-2 * s)) * g y := by
  refine (setLIntegral_le_lintegral _ _).trans_eq ?_
  have hm : Measurable (Function.uncurry (fun x y : ℝ => hardyAveragingKernel s x y * g y)) :=
    (measurable_hardyAveragingKernel s).mul (hg.comp measurable_snd)
  rw [lintegral_lintegral_swap hm.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro y hy
  dsimp only
  have hk : Measurable (fun x => hardyAveragingKernel s x y) :=
    (measurable_hardyAveragingKernel s).comp (measurable_id.prodMk measurable_const)
  rw [lintegral_mul_const'' _ hk.aemeasurable,
    lintegral_hardyAveragingKernel hs (hδ.trans_lt hy.1), mul_assoc]

/-- On a truncated averaging row, restriction to the ambient interval loses no kernel mass. -/
theorem lintegral_hardyAveragingKernel_row_restrict {s δ L x : ℝ} (hδ : 0 ≤ δ)
    (hx : x ∈ Ioo δ (L / 2)) :
    (∫⁻ y : ℝ in Ioo δ L, hardyAveragingKernel s x y) = ENNReal.ofReal (x ^ (-2 * s)) := by
  rw [setLIntegral_eq_of_support_subset (show Function.support (hardyAveragingKernel s x) ⊆ Ioo δ L from ?_),
    lintegral_hardyAveragingKernel_row s (hδ.trans_lt hx.1)]
  intro y hy
  by_contra h
  have hn : y ∉ Ioo x (2 * x) := fun hy => h (hardy_triangle_mem_interval hx hy)
  exact hy (by rw [hardyAveragingKernel_row, indicator_of_notMem hn])

end NLS.Fourier
