import NLS.ZakharovShabat.SourceDiscriminantVariationCircle

/-!
# Integration by parts for the action-gradient integrand

The source derivative of the weighted critical-root quotient has a
closed-circle integral equal to the negative unweighted variation
quotient. This is the contour simplification in Lemma 11.1, before
identifying the integral with the derivative of the action itself.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Contour integration by parts converts the source derivative of
the action integrand to the unweighted discriminant variation. -/
theorem circleIntegral_sourceCriticalRootRatio_sourceFDeriv_eq_neg_variation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (h : CoeffPair p) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hcircle : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    (∮ z in C(c,R), z *
      (fderiv ℂ (fun ψ : CoeffPair p =>
        sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h) =
      -(∮ z in C(c,R),
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
          sourceCanonicalRoot hp hp1 φ z) := by
  calc
    (∮ z in C(c,R), z *
        (fderiv ℂ (fun ψ : CoeffPair p =>
          sourceCriticalRootRatioJoint hp hp1 (z,ψ)) φ) h) =
        ∮ z in C(c,R), z * deriv (fun w : ℂ =>
          (fderiv ℂ (fun ψ : CoeffPair p =>
            canonicalDiscriminant hp (periodOnePotential ψ) w) φ) h /
            sourceCanonicalRoot hp hp1 φ w) z := by
      apply circleIntegral.integral_congr hR
      intro z hz
      dsimp only
      rw [fderiv_sourceCriticalRootRatioJoint_eq_deriv_sourceDiscriminant_div_root
        hp hp1 φ hφ z (hcircle hz) h]
    _ = _ := circleIntegral_mul_deriv_sourceDiscriminantVariation_div_root_eq_neg
      hp hp1 φ h c R hR hcircle

end NLS.ZakharovShabat
