import NLS.ComplexAnalysis.HolomorphicCurveHomotopy

/-!
# Vertical segment integrals

The complex curve integral of a scalar one-form on a vertical segment
is a real interval integral with its imaginary Jacobian. The formula
also applies when the scalar function is singular at the initial
endpoint but integrable on the segment.
-/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis

/-- Parametrize the segment from `c` to `c + y I` by its signed
vertical displacement. -/
theorem curveIntegral_verticalSegment (f : ℂ → ℂ) (c : ℂ) (y : ℝ) :
    (∫ᶜ z in Path.segment c (c + (y:ℂ)*I), holomorphicOneForm f z) =
      (∫ v in (0:ℝ)..y, f (c + (v:ℂ)*I)) * I := by
  have hline (u : ℝ) :
      AffineMap.lineMap c (c + (y:ℂ)*I) u =
        c + ((y*u:ℝ):ℂ)*I := by
    rw [AffineMap.lineMap_apply_module']
    simp only [Complex.real_smul]
    push_cast
    ring
  calc
    (∫ᶜ z in Path.segment c (c + (y:ℂ)*I), holomorphicOneForm f z) =
        ∫ u in (0:ℝ)..1, y • (f (c + (((y*u:ℝ):ℂ)*I)) * I) := by
      rw [curveIntegral_segment]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [hline]
      simp only [holomorphicOneForm_apply]
      simp only [add_sub_cancel_left]
      simp only [Complex.real_smul]
      ring
    _ = y • ∫ u in (0:ℝ)..1, f (c + (((y*u:ℝ):ℂ)*I)) * I := by
      rw [intervalIntegral.integral_smul]
    _ = ∫ v in (0:ℝ)..y, f (c + (v:ℂ)*I) * I := by
      have h := intervalIntegral.smul_integral_comp_mul_add
        (f := fun v : ℝ => f (c + (v:ℂ)*I) * I)
        (a := 0) (b := 1) y (0:ℝ)
      simpa only [mul_zero, zero_add, mul_one, add_zero] using h
    _ = (∫ v in (0:ℝ)..y, f (c + (v:ℂ)*I)) * I := by
      rw [intervalIntegral.integral_mul_const]

/-- Integrability in the vertical coordinate gives genuine curve
integrability, including when `f` is singular at `c`. -/
theorem curveIntegrable_verticalSegment_of_intervalIntegrable
    (f : ℂ → ℂ) (c : ℂ) (y : ℝ) (hy : 0 < y)
    (hint : IntervalIntegrable (fun v : ℝ => f (c + (v:ℂ)*I))
      MeasureTheory.volume 0 y) :
    CurveIntegrable (holomorphicOneForm f) (Path.segment c (c + (y:ℂ)*I)) := by
  rw [curveIntegrable_segment]
  have hcomp := hint.comp_mul_left (c := y)
  have hcomp' : IntervalIntegrable
      (fun u : ℝ => f (c + (((y*u:ℝ):ℂ)*I))) MeasureTheory.volume 0 1 := by
    simpa [hy.ne', div_self] using hcomp
  have hmul := hcomp'.mul_const ((y:ℂ)*I)
  convert hmul using 1
  ext u
  rw [AffineMap.lineMap_apply_module']
  simp only [holomorphicOneForm_apply, Complex.real_smul]
  push_cast
  ring_nf

/-- The downward segment has the opposite imaginary orientation. -/
theorem curveIntegral_downwardSegment (f : ℂ → ℂ) (c : ℂ) (y : ℝ) :
    (∫ᶜ z in Path.segment c (c + ((-y:ℝ):ℂ)*I), holomorphicOneForm f z) =
      -((∫ v in (0:ℝ)..y, f (c + ((-v:ℝ):ℂ)*I)) * I) := by
  rw [curveIntegral_verticalSegment]
  have h := intervalIntegral.smul_integral_comp_mul_add
    (f := fun v : ℝ => f (c + (v:ℂ)*I))
    (a := 0) (b := y) (-1:ℝ) (0:ℝ)
  have heq :
      ∫ v in (0:ℝ)..(-y), f (c + (v:ℂ)*I) =
        -(∫ v in (0:ℝ)..y, f (c + ((-v:ℝ):ℂ)*I)) := by
    simpa only [neg_mul, one_mul, mul_zero, zero_add, neg_zero,
      neg_one_smul, neg_one_mul, add_zero] using h.symm
  rw [heq]
  ring

/-- Integrability in positive downward distance likewise gives
curve integrability of a segment starting at its singular endpoint. -/
theorem curveIntegrable_downwardSegment_of_intervalIntegrable
    (f : ℂ → ℂ) (c : ℂ) (y : ℝ) (hy : 0 < y)
    (hint : IntervalIntegrable (fun v : ℝ => f (c + ((-v:ℝ):ℂ)*I))
      MeasureTheory.volume 0 y) :
    CurveIntegrable (holomorphicOneForm f)
      (Path.segment c (c + ((-y:ℝ):ℂ)*I)) := by
  rw [curveIntegrable_segment]
  have hcomp := hint.comp_mul_left (c := y)
  have hcomp' : IntervalIntegrable
      (fun u : ℝ => f (c + ((-(y*u):ℝ):ℂ)*I)) MeasureTheory.volume 0 1 := by
    simpa [hy.ne', div_self] using hcomp
  have hmul := hcomp'.mul_const (((-y:ℝ):ℂ)*I)
  convert hmul using 1
  ext u
  rw [AffineMap.lineMap_apply_module']
  simp only [holomorphicOneForm_apply, Complex.real_smul]
  push_cast
  ring_nf

end NLS.ComplexAnalysis
