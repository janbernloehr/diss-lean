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
