import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Banach-valued integrals around rectangles

The four oriented edge integrals traverse the bottom, right, top, and left
edges counterclockwise when the opposite corners are ordered. Integrability,
bounded linear maps, and Cauchy's theorem are formulated for the actual
operator-norm Bochner integral.
-/

noncomputable section
open Complex Set MeasureTheory
namespace NLS.RectangleIntegral

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℂ E] [NormedSpace ℂ F]

/-- Four oriented edge integrals, with opposite corners `z` and `w`. -/
def integral (f : ℂ → E) (z w : ℂ) : E :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
  (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
  I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
  I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- The boundary includes every endpoint of all four edges. -/
def boundary (z w : ℂ) : Set ℂ :=
  {ζ | ζ.re ∈ uIcc z.re w.re ∧ ζ.im ∈ uIcc z.im w.im ∧
    (ζ.re = z.re ∨ ζ.re = w.re ∨ ζ.im = z.im ∨ ζ.im = w.im)}

/-- Each contour point belongs to the corresponding closed rectangle. -/
theorem boundary_subset_rectangle (z w : ℂ) :
    boundary z w ⊆ uIcc z.re w.re ×ℂ uIcc z.im w.im :=
  fun _ h => ⟨h.1, h.2.1⟩

/-- For ordered corners, a point in the closed rectangle but outside its interior is on the boundary. -/
theorem mem_boundary_of_mem_rectangle_of_not_mem_open {z w a : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hc : a ∈ uIcc z.re w.re ×ℂ uIcc z.im w.im)
    (ho : a ∉ Ioo z.re w.re ×ℂ Ioo z.im w.im) : a ∈ boundary z w := by
  refine ⟨hc.1, hc.2, ?_⟩
  have hr := hc.1
  have hi := hc.2
  rw [uIcc_of_le hre] at hr
  rw [uIcc_of_le him] at hi
  by_contra hne
  simp only [not_or] at hne
  exact ho ⟨⟨lt_of_le_of_ne hr.1 (Ne.symm hne.1), lt_of_le_of_ne hr.2 hne.2.1⟩,
    ⟨lt_of_le_of_ne hi.1 (Ne.symm hne.2.2.1), lt_of_le_of_ne hi.2 hne.2.2.2⟩⟩

/-- Integrability of the four edge parameterizations. -/
structure Integrable (f : ℂ → E) (z w : ℂ) : Prop where
  bottom : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re
  top : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re
  right : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im
  left : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im

/-- Every point on either horizontal edge lies on the rectangular boundary. -/
theorem horizontal_mem (z w : ℂ) {x y : ℝ} (hx : x ∈ uIcc z.re w.re)
    (hy : y = z.im ∨ y = w.im) : (x : ℂ) + y * I ∈ boundary z w := by
  rcases hy with rfl | rfl <;>
    simp [boundary, hx, left_mem_uIcc, right_mem_uIcc]

/-- Every point on either vertical edge lies on the rectangular boundary. -/
theorem vertical_mem (z w : ℂ) {x y : ℝ} (hy : y ∈ uIcc z.im w.im)
    (hx : x = z.re ∨ x = w.re) : (x : ℂ) + y * I ∈ boundary z w := by
  rcases hx with rfl | rfl <;>
    simp [boundary, hy, left_mem_uIcc, right_mem_uIcc]

omit [NormedSpace ℂ E] in
/-- Continuity on the boundary suffices; the interior may contain poles. -/
theorem integrable_of_continuousOn {f : ℂ → E} {z w : ℂ}
    (hf : ContinuousOn f (boundary z w)) : Integrable f z w := by
  have hh (y : ℝ) (hy : y = z.im ∨ y = w.im) :
      IntervalIntegrable (fun x : ℝ => f (x + y * I)) volume z.re w.re :=
    (hf.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun _ hx => horizontal_mem z w hx hy)).intervalIntegrable
  have hv (x : ℝ) (hx : x = z.re ∨ x = w.re) :
      IntervalIntegrable (fun y : ℝ => f (x + y * I)) volume z.im w.im :=
    (hf.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun _ hy => vertical_mem z w hy hx)).intervalIntegrable
  exact ⟨hh _ (Or.inl rfl), hh _ (Or.inr rfl), hv _ (Or.inr rfl), hv _ (Or.inl rfl)⟩

/-- Boundary equality determines the actual integral, regardless of interior values. -/
theorem congr {f g : ℂ → E} {z w : ℂ} (h : EqOn f g (boundary z w)) :
    integral f z w = integral g z w := by
  have hh (y : ℝ) (hy : y = z.im ∨ y = w.im) :
      (∫ x : ℝ in z.re..w.re, f (x + y * I)) = ∫ x : ℝ in z.re..w.re, g (x + y * I) :=
    intervalIntegral.integral_congr fun _ hx => h (horizontal_mem z w hx hy)
  have hv (x : ℝ) (hx : x = z.re ∨ x = w.re) :
      (∫ y : ℝ in z.im..w.im, f (x + y * I)) = ∫ y : ℝ in z.im..w.im, g (x + y * I) :=
    intervalIntegral.integral_congr fun _ hy => h (vertical_mem z w hy hx)
  simp only [integral, hh _ (Or.inl rfl), hh _ (Or.inr rfl), hv _ (Or.inl rfl), hv _ (Or.inr rfl)]

/-- Splitting across a horizontal line cancels the shared edge, including its orientation. -/
theorem split_horizontal {f : ℂ → E} {z w : ℂ} (c : ℝ)
    (h₁ : Integrable f z ⟨w.re, c⟩) (h₂ : Integrable f ⟨z.re, c⟩ w) :
    integral f z w = integral f z ⟨w.re, c⟩ + integral f ⟨z.re, c⟩ w := by
  have hr := intervalIntegral.integral_add_adjacent_intervals h₁.right h₂.right
  have hl := intervalIntegral.integral_add_adjacent_intervals h₁.left h₂.left
  dsimp only at hr hl
  simp only [integral]
  rw [← hr, ← hl, smul_add, smul_add]
  abel

/-- Splitting across a vertical line cancels the oppositely traversed shared edge. -/
theorem split_vertical {f : ℂ → E} {z w : ℂ} (c : ℝ)
    (h₁ : Integrable f z ⟨c, w.im⟩) (h₂ : Integrable f ⟨c, z.im⟩ w) :
    integral f z w = integral f z ⟨c, w.im⟩ + integral f ⟨c, z.im⟩ w := by
  have hb := intervalIntegral.integral_add_adjacent_intervals h₁.bottom h₂.bottom
  have ht := intervalIntegral.integral_add_adjacent_intervals h₁.top h₂.top
  dsimp only at hb ht
  simp only [integral]
  rw [← hb, ← ht]
  abel

/-- Subtraction commutes with the four-edge integral when both integrands are integrable. -/
theorem integral_sub {f g : ℂ → E} {z w : ℂ} (hf : Integrable f z w) (hg : Integrable g z w) :
    integral (fun ζ => f ζ - g ζ) z w = integral f z w - integral g z w := by
  simp only [integral, intervalIntegral.integral_sub hf.bottom hg.bottom,
    intervalIntegral.integral_sub hf.top hg.top, intervalIntegral.integral_sub hf.right hg.right,
    intervalIntegral.integral_sub hf.left hg.left, smul_sub]
  abel

variable [CompleteSpace E] [CompleteSpace F]

omit [CompleteSpace F] in
/-- A constant vector can be taken outside a scalar rectangular integral. -/
theorem integral_smul_const (f : ℂ → ℂ) (z w : ℂ) (v : E) :
    integral (fun ζ => f ζ • v) z w = integral f z w • v := by
  simp only [integral, intervalIntegral.integral_smul_const, sub_smul, add_smul, smul_smul, smul_eq_mul]

/-- Bounded complex-linear maps commute with rectangular integration. -/
theorem map (A : E →L[ℂ] F) {f : ℂ → E} {z w : ℂ} (hf : Integrable f z w) :
    A (integral f z w) = integral (fun ζ => A (f ζ)) z w := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
  simp only [integral, map_sub, map_add, map_smul,
    ← A.intervalIntegral_comp_comm hf.bottom, ← A.intervalIntegral_comp_comm hf.top,
    ← A.intervalIntegral_comp_comm hf.right, ← A.intervalIntegral_comp_comm hf.left]

omit [CompleteSpace E] in
/-- Evaluation commutes with an operator-norm rectangular integral. -/
theorem apply {f : ℂ → E →L[ℂ] F} {z w : ℂ} (hf : Integrable f z w) (x : E) :
    integral f z w x = integral (fun ζ => f ζ x) z w :=
  map (ContinuousLinearMap.apply ℂ F x) hf

omit [CompleteSpace E] [CompleteSpace F] in
/-- Cauchy's theorem for an analytic rectangle, with no interior spectral points. -/
theorem eq_zero_of_differentiableOn {f : ℂ → E} {z w : ℂ}
    (hf : DifferentiableOn ℂ f (uIcc z.re w.re ×ℂ uIcc z.im w.im)) :
    integral f z w = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf

omit [CompleteSpace E] [CompleteSpace F] in
/-- Removing an analytic horizontal strip does not change the contour integral. -/
theorem eq_of_horizontal_strip {f : ℂ → E} {z w : ℂ} (c : ℝ)
    (h₁ : Integrable f z ⟨w.re, c⟩)
    (h₂ : DifferentiableOn ℂ f (uIcc z.re w.re ×ℂ uIcc c w.im)) :
    integral f z w = integral f z ⟨w.re, c⟩ := by
  have hi : Integrable f ⟨z.re, c⟩ w :=
    integrable_of_continuousOn (h₂.continuousOn.mono (boundary_subset_rectangle ⟨z.re, c⟩ w))
  rw [split_horizontal c h₁ hi, eq_zero_of_differentiableOn (z := ⟨z.re, c⟩) (w := w) h₂, add_zero]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Removing an analytic vertical strip does not change the contour integral. -/
theorem eq_of_vertical_strip {f : ℂ → E} {z w : ℂ} (c : ℝ)
    (h₁ : Integrable f z ⟨c, w.im⟩)
    (h₂ : DifferentiableOn ℂ f (uIcc c w.re ×ℂ uIcc z.im w.im)) :
    integral f z w = integral f z ⟨c, w.im⟩ := by
  have hi : Integrable f ⟨c, z.im⟩ w :=
    integrable_of_continuousOn (h₂.continuousOn.mono (boundary_subset_rectangle ⟨c, z.im⟩ w))
  rw [split_vertical c h₁ hi, eq_zero_of_differentiableOn (z := ⟨c, z.im⟩) (w := w) h₂, add_zero]

end NLS.RectangleIntegral
