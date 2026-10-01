import NLS.ZakharovShabat.SourceActionPoissonGradient

/-! # Action contours paired with arbitrary actual cotangents

The action's proved Banach-valued contour formula can be paired with
any source cotangent. In particular, it applies to the differential of
the actual angle/angle bracket, rather than just an angle differential.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any actual scalar functional's bracket with an action is the
canonical-root-weighted contour of its discriminant brackets. -/
theorem sourceBracket_functional_action_eq_discriminant_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (F : CoeffPair p → ℂ) (k : ℤ) (ch : SourceRealActionBallChart hp hp1 k)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    sourceBracket h2p F (sourceComplexAction hp hp1 k) φ =
      -(Real.pi : ℂ)⁻¹*(∮ z in C(ch.spectralCenter,ch.spectralRadius),
        sourceBracket h2p F
          (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ /
            sourceCanonicalRoot hp hp1 φ z) := by
  have hgeom := ch.geometry φ hφ
  have hcircle := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ k
    ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  have hint := circleIntegrable_sourceActionVariationCotangent hp hp1 φ
    ch.spectralCenter ch.spectralRadius ch.spectralRadius_pos.le hcircle
  rw [sourceBracket,fderiv_sourceComplexAction_eq_cotangent_circle_on_chart hp hp1 k ch φ hreal hφ]
  simp only [map_smul,smul_eq_mul]
  rw [map_circleIntegral (sourceBivector h2p (fderiv ℂ F φ)) hint]
  congr 1
  apply circleIntegral.integral_congr ch.spectralRadius_pos.le
  intro z _
  simp only [sourceActionVariationCotangent,sourceDiscriminantCotangent,
    sourceBracket,map_smul,smul_eq_mul,div_eq_mul_inv,mul_comm]

end NLS.ZakharovShabat
