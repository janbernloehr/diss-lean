import NLS.SequenceSpaces.HilbertMatrixTranspose
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Constructions

/-! # Analytic bilinear Hilbert transpose evaluation -/
noncomputable section
open Set Complex
namespace NLS.Coeff

/-- Transposing a bounded operator preserves its bound on every Hilbert vector. -/
theorem norm_hilbertMatrixTranspose_apply_le (A : Coeff 2 →L[ℂ] Coeff 2) (a : Coeff 2) :
    ‖hilbertMatrixTranspose A a‖ ≤ ‖A‖ * ‖a‖ := by
  change ‖hilbertCotangentCoefficients ((dualPairing a).comp A)‖ ≤ _
  rw [norm_hilbertCotangentCoefficients]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  exact (norm_dualPairing_le a (A b)).trans
    ((mul_le_mul_of_nonneg_left (A.le_opNorm b) (norm_nonneg a)).trans_eq (by ring))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Analytic operator and vector families give a native analytic transposed
vector family, without any coordinatewise-to-norm inference. -/
theorem analyticAt_hilbertMatrixTranspose_apply
    {A : E → Coeff 2 →L[ℂ] Coeff 2} {a : E → Coeff 2} {x : E}
    (hA : AnalyticAt ℂ A x) (ha : AnalyticAt ℂ a x) :
    AnalyticAt ℂ (fun y => hilbertMatrixTranspose (A y) (a y)) x := by
  have hdual : AnalyticAt ℂ (fun y => dualPairing (a y)) x :=
    ((dualPairing (p := 2) (q := 2)).analyticAt _).comp ha
  have hcomp : AnalyticAt ℂ (fun y => (dualPairing (a y)).comp (A y)) x :=
    ((ContinuousLinearMap.compL ℂ (Coeff 2) (Coeff 2) ℂ).analyticAt_bilinear _).comp
      (f := fun y => (dualPairing (a y), A y)) (hdual.prod hA)
  exact (hilbertCotangentCoefficients.analyticAt _).comp hcomp

end NLS.Coeff
