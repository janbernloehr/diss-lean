import NLS.ZakharovShabat.SourceComplexActionGradient
import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Operator-valued discriminant variations

The full source differential of the discriminant is jointly analytic
with values in the continuous cotangent space. Dividing it by the
canonical root gives an operator-valued analytic spectral integrand
off the periodic cuts, so its circle integral is a genuine cotangent.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceDiscriminantCotangent (hp : p ≠ ⊤) (z : ℂ) (ψ : CoeffPair p) :
    CoeffPair p →L[ℂ] ℂ :=
  fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ

theorem analyticOnNhd_sourceDiscriminantCotangent_joint (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ
      (fun t : ℂ × CoeffPair p => sourceDiscriminantCotangent hp t.1 t.2) univ := by
  let F : ℂ × CoeffPair p → ℂ := fun t =>
    canonicalDiscriminant hp (periodOnePotential t.2) t.1
  have hF : AnalyticOnNhd ℂ F univ := analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
  have hG := analyticOnNhd_parameterDerivative F hF
  have heq : (fun t : ℂ × CoeffPair p => sourceDiscriminantCotangent hp t.1 t.2) =
      (fun t => (fderiv ℂ F t).comp (ContinuousLinearMap.inr ℂ ℂ (CoeffPair p))) := by
    funext t
    exact fderiv_source_section_eq_joint F t.1 t.2 ((hF t (mem_univ _)).differentiableAt)
  rw [heq]
  exact hG

def sourceActionVariationCotangent (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) : CoeffPair p →L[ℂ] ℂ :=
  (sourceCanonicalRoot hp hp1 ψ z)⁻¹ • sourceDiscriminantCotangent hp z ψ

theorem analyticOnNhd_sourceActionVariationCotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    AnalyticOnNhd ℂ (sourceActionVariationCotangent hp hp1 ψ)
      (sourceCanonicalRootDomain hp hp1 ψ) := by
  intro z hz
  have hcot := ((analyticOnNhd_sourceDiscriminantCotangent_joint hp hp1)
    (z,ψ) (mem_univ _)).comp (f := fun w : ℂ => (w,ψ))
      (analyticAt_id.prod analyticAt_const)
  exact ((sourceCanonicalRoot_analyticOnNhd hp hp1 ψ z hz).inv
    (sourceCanonicalRoot_ne_zero_off_gaps hp hp1 ψ z hz)).smul hcot

theorem circleIntegrable_sourceActionVariationCotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    CircleIntegrable (sourceActionVariationCotangent hp hp1 ψ) c R :=
  ((analyticOnNhd_sourceActionVariationCotangent hp hp1 ψ).continuousOn.mono hcircle).circleIntegrable hR

end NLS.ZakharovShabat
