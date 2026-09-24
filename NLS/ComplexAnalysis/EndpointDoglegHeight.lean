import NLS.ComplexAnalysis.HorizontalSegmentIntegral
import NLS.FunctionalAnalysis.RectangleIntegral

/-!
# Height invariance of endpoint dogleg values

The two vertical pieces of a dogleg start at the same fixed real
endpoints. Splitting their integrals between two positive heights and
applying Cauchy's theorem to the intervening rectangle shows that the
total value does not change with height.
-/

noncomputable section
open Set Complex MeasureTheory
namespace NLS.ComplexAnalysis

/-- The coordinate expression for a path up from `a`, across at
height `y`, and down to `b`. -/
def upperDoglegValue (f : ℂ → ℂ) (a b y : ℝ) : ℂ :=
  (∫ v in (0:ℝ)..y, f ((a:ℂ)+(v:ℂ)*I)) * I +
  (∫ x in a..b, f ((x:ℂ)+(y:ℂ)*I)) -
  (∫ v in (0:ℝ)..y, f ((b:ℂ)+(v:ℂ)*I)) * I

/-- Cauchy's rectangle identity makes the dogleg value independent
of height once both singular endpoint integrals exist. -/
theorem upperDoglegValue_eq_of_rectangle
    (f : ℂ → ℂ) (a b y z : ℝ)
    (h0y : 0 ≤ y) (hyz : y ≤ z)
    (ha : IntervalIntegrable (fun v : ℝ => f ((a:ℂ)+(v:ℂ)*I)) volume 0 z)
    (hb : IntervalIntegrable (fun v : ℝ => f ((b:ℂ)+(v:ℂ)*I)) volume 0 z)
    (hf : DifferentiableOn ℂ f
      (uIcc a b ×ℂ uIcc y z)) :
    upperDoglegValue f a b y = upperDoglegValue f a b z := by
  have hy_mem : y ∈ uIcc (0:ℝ) z := by
    rw [uIcc_of_le (h0y.trans hyz)]
    exact ⟨h0y,hyz⟩
  have ha0y := ha.mono_set (uIcc_subset_uIcc_left hy_mem)
  have hayz := ha.mono_set (uIcc_subset_uIcc_right hy_mem)
  have hb0y := hb.mono_set (uIcc_subset_uIcc_left hy_mem)
  have hbyz := hb.mono_set (uIcc_subset_uIcc_right hy_mem)
  have haadd := intervalIntegral.integral_add_adjacent_intervals ha0y hayz
  have hbadd := intervalIntegral.integral_add_adjacent_intervals hb0y hbyz
  have hrect := NLS.RectangleIntegral.eq_zero_of_differentiableOn
    (z := (⟨a,y⟩:ℂ)) (w := (⟨b,z⟩:ℂ)) hf
  dsimp [NLS.RectangleIntegral.integral] at hrect
  unfold upperDoglegValue
  rw [← haadd, ← hbadd]
  linear_combination hrect

/-- The same rectangle argument applies to signed heights. This
version directly supports doglegs below the real axis. -/
theorem upperDoglegValue_eq_of_rectangle_signed
    (f : ℂ → ℂ) (a b y z : ℝ)
    (ha_y : IntervalIntegrable (fun v : ℝ => f ((a:ℂ)+(v:ℂ)*I)) volume 0 y)
    (ha_z : IntervalIntegrable (fun v : ℝ => f ((a:ℂ)+(v:ℂ)*I)) volume 0 z)
    (hb_y : IntervalIntegrable (fun v : ℝ => f ((b:ℂ)+(v:ℂ)*I)) volume 0 y)
    (hb_z : IntervalIntegrable (fun v : ℝ => f ((b:ℂ)+(v:ℂ)*I)) volume 0 z)
    (hf : DifferentiableOn ℂ f (uIcc a b ×ℂ uIcc y z)) :
    upperDoglegValue f a b y = upperDoglegValue f a b z := by
  have haadd := intervalIntegral.integral_add_adjacent_intervals
    ha_y (ha_y.symm.trans ha_z)
  have hbadd := intervalIntegral.integral_add_adjacent_intervals
    hb_y (hb_y.symm.trans hb_z)
  have hrect := NLS.RectangleIntegral.eq_zero_of_differentiableOn
    (z := (⟨a,y⟩:ℂ)) (w := (⟨b,z⟩:ℂ)) hf
  dsimp [NLS.RectangleIntegral.integral] at hrect
  unfold upperDoglegValue
  rw [← haadd, ← hbadd]
  linear_combination hrect

/-- A downward-distance integrability hypothesis is equivalent to
integrability in the signed negative vertical coordinate. -/
theorem intervalIntegrable_signed_vertical_of_downward
    (f : ℂ → ℂ) (a y : ℝ)
    (hint : IntervalIntegrable
      (fun v : ℝ => f ((a:ℂ)+((-v:ℝ):ℂ)*I)) volume 0 y) :
    IntervalIntegrable
      (fun v : ℝ => f ((a:ℂ)+(v:ℂ)*I)) volume 0 (-y) := by
  have h := (IntervalIntegrable.iff_comp_neg).mp hint
  simpa only [neg_zero, neg_neg] using h

end NLS.ComplexAnalysis
