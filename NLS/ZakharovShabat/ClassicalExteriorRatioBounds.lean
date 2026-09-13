import NLS.ZakharovShabat.FreeStripInverseBounds
import NLS.ZakharovShabat.ClassicalHorizontalStripBounds
import NLS.ZakharovShabat.ClassicalHalfPlaneAsymptotics
import NLS.ZakharovShabat.UniformThresholds

/-!
# Classical/free ratio bounds outside the free discs

The half-plane limits give uniform bounds above and below a fixed strip.
Inside the strip, the global trace estimate and periodic free inverse bound
supply the missing bound, without restricting the real spectral parameter.
-/

noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Both shifted classical/free ratios are uniformly bounded off fixed free discs. -/
theorem exists_bound_classicalDiscriminant_sub_div_free
    (Φ : Curve (ℂ × ℂ)) (b : ℂ) (hb : b^2 = 4) {r : ℝ} (hr : 0 < r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ,
      (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      ‖(classicalDiscriminant Φ z-b)/(freeDiscriminant z-b)‖ ≤ B := by
  let f := fun z : ℂ => (classicalDiscriminant Φ z-b)/(freeDiscriminant z-b)
  obtain ⟨U, hU⟩ := exists_threshold_norm_le_two (fun z : ℂ => z.im) f
    (tendsto_classicalDiscriminant_sub_div_free_upper Φ id tendsto_comap b)
  have hl : Tendsto (fun z : ℂ => z.im)
      (comap (fun z : ℂ => -z.im) atTop) atBot := by
    simpa only [Function.comp_def, neg_neg] using tendsto_neg_atTop_atBot.comp
      (tendsto_comap : Tendsto (fun z : ℂ => -z.im)
        (comap (fun z : ℂ => -z.im) atTop) atTop)
  obtain ⟨L, hL⟩ := exists_threshold_norm_le_two (fun z : ℂ => -z.im) f
    (tendsto_classicalDiscriminant_sub_div_free_lower Φ id hl b)
  let H := max U L
  obtain ⟨C, hC, hbound⟩ := exists_bound_freeDiscriminant_sub_inv_strip b hb hr H
  let D := (2*Real.exp (H+‖Φ‖)+‖b‖)*C
  refine ⟨max 2 D, (by positivity), ?_⟩
  intro z hz
  by_cases hu : U ≤ z.im
  · exact (hU z hu).trans (le_max_left _ _)
  by_cases hl : L ≤ -z.im
  · exact (hL z hl).trans (le_max_left _ _)
  have hs : |z.im| ≤ H := abs_le.mpr ⟨by dsimp [H]; linarith [le_max_right U L],
    by dsimp [H]; linarith [le_max_left U L]⟩
  have hn : ‖classicalDiscriminant Φ z-b‖ ≤ 2*Real.exp (H+‖Φ‖)+‖b‖ :=
    (norm_sub_le _ _).trans (add_le_add
      (norm_classicalDiscriminant_le_of_bounds Φ z ‖Φ‖ H le_rfl hs) le_rfl)
  calc
    ‖(classicalDiscriminant Φ z-b)/(freeDiscriminant z-b)‖ =
        ‖classicalDiscriminant Φ z-b‖*‖(freeDiscriminant z-b)⁻¹‖ := by rw [div_eq_mul_inv, norm_mul]
    _ ≤ D := mul_le_mul hn (hbound z hs hz) (norm_nonneg _) (by positivity)
    _ ≤ max 2 D := le_max_right _ _

end NLS.ZakharovShabat
