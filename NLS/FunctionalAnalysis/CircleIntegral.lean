import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Continuous linear maps and circle integrals

Evaluation and bounded linear maps commute with Banach-valued circle integrals.
These bridges let operator-norm integrals act on vectors without replacing
the operator integral by a merely pointwise construction.
-/

noncomputable section

namespace NLS.CircleIntegral

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

/-- Bounded complex-linear maps commute with circle integration. -/
theorem map (A : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) :
    A (∮ z in C(c, r), f z) = ∮ z in C(c, r), A (f z) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
  simp only [circleIntegral]
  rw [← A.intervalIntegral_comp_comm hf.out]
  simp only [map_smul]

omit [CompleteSpace E] in
/-- Evaluate an operator-valued circle integral on a vector. -/
theorem apply {f : ℂ → E →L[ℂ] F} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) (x : E) :
    (∮ z in C(c, r), f z) x = ∮ z in C(c, r), f z x :=
  map (ContinuousLinearMap.apply ℂ F x) hf

end NLS.CircleIntegral

namespace NLS.CircleIntegral

open Complex Metric MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Exchange two circle integrals of a continuous function on the product of circles. -/
theorem swap {f : ℂ → ℂ → E} {c d : ℂ} {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hf : ContinuousOn (Function.uncurry f) (sphere c r ×ˢ sphere d R)) :
    (∮ z in C(c, r), ∮ w in C(d, R), f z w) =
      ∮ w in C(d, R), ∮ z in C(c, r), f z w := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  let g : ℝ × ℝ → E := fun t => deriv (circleMap c r) t.1 •
    deriv (circleMap d R) t.2 • f (circleMap c r t.1) (circleMap d R t.2)
  have hfc : Continuous (fun t : ℝ × ℝ => f (circleMap c r t.1) (circleMap d R t.2)) :=
    hf.comp_continuous (((continuous_circleMap c r).comp continuous_fst).prodMk
      ((continuous_circleMap d R).comp continuous_snd))
      (fun t => ⟨by simp [abs_of_nonneg hr], by simp [abs_of_nonneg hR]⟩)
  have hg : Continuous g := by
    dsimp [g]
    simp only [deriv_circleMap]
    exact (((continuous_circleMap 0 r).comp continuous_fst).mul continuous_const).smul
      ((((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const).smul hfc)
  have hi : Integrable g ((volume.restrict (Icc 0 (2 * Real.pi))).prod
      (volume.restrict (Icc 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hs := MeasureTheory.integral_integral_swap (f := fun x y => g (x, y)) hi
  simp only [circleIntegral_def_Icc, ← MeasureTheory.integral_smul]
  dsimp only [g] at hs
  rw [hs]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with y
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  exact smul_comm _ _ _

end NLS.CircleIntegral
