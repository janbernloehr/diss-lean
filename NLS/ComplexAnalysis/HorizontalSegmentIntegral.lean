import NLS.ComplexAnalysis.VerticalSegmentIntegral

/-!
# Horizontal segment integrals

The curve integral of a scalar complex one-form along a horizontal
segment is the corresponding real-coordinate interval integral. This
lets rectangle identities apply directly to bundled paths.
-/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem curveIntegral_horizontalSegment (f : ℂ → ℂ) (a b y : ℝ) :
    (∫ᶜ z in Path.segment ((a:ℂ)+(y:ℂ)*I) ((b:ℂ)+(y:ℂ)*I),
      holomorphicOneForm f z) =
      ∫ x in a..b, f ((x:ℂ)+(y:ℂ)*I) := by
  let g : ℝ → ℂ := fun x => f ((x:ℂ)+(y:ℂ)*I)
  have hline (u : ℝ) :
      AffineMap.lineMap ((a:ℂ)+(y:ℂ)*I) ((b:ℂ)+(y:ℂ)*I) u =
        (((b-a)*u+a:ℝ):ℂ)+(y:ℂ)*I := by
    rw [AffineMap.lineMap_apply_module']
    simp only [Complex.real_smul]
    push_cast
    ring
  calc
    (∫ᶜ z in Path.segment ((a:ℂ)+(y:ℂ)*I) ((b:ℂ)+(y:ℂ)*I),
      holomorphicOneForm f z) =
        (b-a) • ∫ u in (0:ℝ)..1, g ((b-a)*u+a) := by
      rw [curveIntegral_segment, ← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [hline]
      simp only [holomorphicOneForm_apply]
      dsimp [g]
      push_cast
      ring
    _ = ∫ x in a..b, g x := by
      have h := intervalIntegral.smul_integral_comp_mul_add
        (f := g) (a := 0) (b := 1) (b-a) a
      simpa only [mul_zero, zero_add, mul_one, sub_add_cancel] using h
    _ = _ := rfl

end NLS.ComplexAnalysis
