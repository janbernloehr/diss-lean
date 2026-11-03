import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring

/-! # Classical time-dependent translation for mKdV

Pointwise chain-rule identification of equations (1) and (2) of
arXiv:1606.07052v1. The mass parameter is fixed. To obtain a PDE solution
statement it must additionally be identified with the conserved integral
of the square of the solution. No low-regularity solution claim is made here.
-/
noncomputable section
namespace NLS.Articles.MKdVBelowL2

/-- Time-space differential with the original mKdV velocity as its time component. -/
def originalDifferential (v ux uxxx : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (-uxxx + 6 * v ^ 2 * ux) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    ux • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Translating an original classical solution by `x - 6 M t` gives the
renormalized velocity. `hu` specifies the actual time-space derivative. -/
theorem hasDerivAt_renormalizing_translation
    (u : ℝ × ℝ → ℝ) (M t x ux uxxx : ℝ)
    (hu : HasFDerivAt u
      (originalDifferential (u (t, x - 6 * M * t)) ux uxxx)
      (t, x - 6 * M * t)) :
    HasDerivAt (fun s : ℝ => u (s, x - 6 * M * s))
      (-uxxx + 6 * ((u (t, x - 6 * M * t)) ^ 2 - M) * ux) t := by
  have hp : HasDerivAt (fun s : ℝ => (s, x - 6 * M * s)) (1, -(6 * M)) t := by
    convert (hasDerivAt_id t).prodMk
      ((hasDerivAt_const t x).sub ((hasDerivAt_id t).const_mul (6 * M))) using 1 <;> simp
  have he : originalDifferential (u (t, x - 6 * M * t)) ux uxxx (1, -(6 * M)) =
      -uxxx + 6 * (u (t, x - 6 * M * t) ^ 2 - M) * ux := by
    change (-uxxx + 6 * u (t, x - 6 * M * t) ^ 2 * ux) * 1 + ux * -(6 * M) = _
    ring
  simpa only [he] using! hu.comp_hasDerivAt t hp


/-- Renormalized time-space differential with an explicitly fixed mass. -/
def renormalizedDifferential (M v ux uxxx : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (-uxxx + 6 * (v ^ 2 - M) * ux) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    ux • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The inverse translation `x + 6 M t` restores the original velocity. -/
theorem hasDerivAt_original_translation
    (u : ℝ × ℝ → ℝ) (M t x ux uxxx : ℝ)
    (hu : HasFDerivAt u
      (renormalizedDifferential M (u (t, x + 6 * M * t)) ux uxxx)
      (t, x + 6 * M * t)) :
    HasDerivAt (fun s : ℝ => u (s, x + 6 * M * s))
      (-uxxx + 6 * (u (t, x + 6 * M * t)) ^ 2 * ux) t := by
  have hp : HasDerivAt (fun s : ℝ => (s, x + 6 * M * s)) (1, 6 * M) t := by
    convert (hasDerivAt_id t).prodMk
      ((hasDerivAt_const t x).add ((hasDerivAt_id t).const_mul (6 * M))) using 1 <;> simp
  have he : renormalizedDifferential M (u (t, x + 6 * M * t)) ux uxxx (1, 6 * M) =
      -uxxx + 6 * u (t, x + 6 * M * t) ^ 2 * ux := by
    change (-uxxx + 6 * (u (t, x + 6 * M * t) ^ 2 - M) * ux) * 1 + ux * (6 * M) = _
    ring
  simpa only [he] using! hu.comp_hasDerivAt t hp

end NLS.Articles.MKdVBelowL2
