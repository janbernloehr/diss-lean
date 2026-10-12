import NLS.SequenceSpaces.SobolevFullDuality
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Analytic scalar gradients on the full real Sobolev scale

The inverse physical duality isometry turns every complex differential into
its unique opposite-order gradient. Analyticity and the full Hessian identity
hold throughout the finite-p Banach range, including p=1.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- The physical scalar gradient operator on all bounded complex functionals. -/
def sobolevCotangentCLM (s : ℝ) (hp : p ≠ ⊤) :
    (WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) →L[ℂ]
      WeightedCoeff (Weight.sobolev (-s)) q :=
  (sobolevDualityIsometry s hp).symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem sobolevCotangentCLM_apply (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) :
    sobolevCotangentCLM (q := q) s hp L = sobolevCotangent s hp L :=
  sobolevDualityIsometry_symm_apply s hp L

/-- Scalar differential represented in the physical unconjugated pairing. -/
def sobolevScalarGradient (s : ℝ) (hp : p ≠ ⊤)
    (F : WeightedCoeff (Weight.sobolev s) p → ℂ) (a : WeightedCoeff (Weight.sobolev s) p) :
    WeightedCoeff (Weight.sobolev (-s)) q :=
  sobolevCotangentCLM s hp (fderiv ℂ F a)

theorem fderiv_eq_sobolevBilinearPairing_gradient (s : ℝ) (hp : p ≠ ⊤)
    (F : WeightedCoeff (Weight.sobolev s) p → ℂ) (a h : WeightedCoeff (Weight.sobolev s) p) :
    fderiv ℂ F a h = sobolevBilinearPairing s h (sobolevScalarGradient (q := q) s hp F a) := by
  simpa only [sobolevScalarGradient,sobolevCotangentCLM_apply] using
    (sobolevBilinearPairing_sobolevCotangent (q := q) s hp (fderiv ℂ F a) h).symm

theorem norm_sobolevScalarGradient (s : ℝ) (hp : p ≠ ⊤)
    (F : WeightedCoeff (Weight.sobolev s) p → ℂ) (a : WeightedCoeff (Weight.sobolev s) p) :
    ‖sobolevScalarGradient (q := q) s hp F a‖ = ‖fderiv ℂ F a‖ := by
  exact (sobolevDualityIsometry s hp).symm.norm_map _

/-- The gradient is analytic on the original scalar analytic domain. -/
theorem analyticOnNhd_sobolevScalarGradient (s : ℝ) (hp : p ≠ ⊤)
    (F : WeightedCoeff (Weight.sobolev s) p → ℂ)
    {U : Set (WeightedCoeff (Weight.sobolev s) p)} (hF : AnalyticOnNhd ℂ F U) :
    AnalyticOnNhd ℂ (sobolevScalarGradient (q := q) s hp F) U := by
  intro a ha
  exact ((sobolevCotangentCLM (q := q) s hp).analyticAt _).comp (hF.fderiv a ha)

/-- Differentiating the gradient represents the complete scalar Hessian. -/
theorem hessian_eq_sobolevBilinearPairing_gradient_derivative (s : ℝ) (hp : p ≠ ⊤)
    (F : WeightedCoeff (Weight.sobolev s) p → ℂ) (a : WeightedCoeff (Weight.sobolev s) p)
    (hF : AnalyticAt ℂ F a) (v h : WeightedCoeff (Weight.sobolev s) p) :
    fderiv ℂ (fderiv ℂ F) a v h =
      sobolevBilinearPairing s h (fderiv ℂ (sobolevScalarGradient (q := q) s hp F) a v) := by
  have hd := ((sobolevCotangentCLM (q := q) s hp).hasFDerivAt.comp a
    hF.fderiv.differentiableAt.hasFDerivAt).fderiv
  have he : fderiv ℂ (sobolevScalarGradient (q := q) s hp F) a v =
      sobolevCotangentCLM s hp (fderiv ℂ (fderiv ℂ F) a v) :=
    congrArg (fun L : WeightedCoeff (Weight.sobolev s) p →L[ℂ]
      WeightedCoeff (Weight.sobolev (-s)) q => L v) hd
  rw [he,sobolevCotangentCLM_apply,sobolevBilinearPairing_sobolevCotangent]

end NLS.WeightedCoeff
