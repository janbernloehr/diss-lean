import NLS.ZakharovShabat.SourceActionCircleGradient
import NLS.ZakharovShabat.SourceComplexAction

/-!
# Gradient of the glued indexed action at real-type sources

Each chart circle represents the glued complex action on an open
source neighborhood. The fixed-circle gradient formula therefore
applies to the indexed action at every real-type source.
-/

noncomputable section
open Set Metric Filter Complex
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any action chart containing a real-type source computes the
Fréchet derivative of the glued indexed action by the contour
gradient formula. -/
theorem fderiv_sourceComplexAction_eq_gradient_on_chart
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ch : SourceRealActionBallChart hp hp1 n)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (hφch : φ ∈ ball ch.center ch.radius)
    (h : CoeffPair p) :
    (fderiv ℂ (sourceComplexAction hp hp1 n) φ) h =
      -(Real.pi : ℂ)⁻¹ *
        (∮ z in C(ch.spectralCenter,ch.spectralRadius),
          (fderiv ℂ (fun ψ : CoeffPair p =>
            canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
            sourceCanonicalRoot hp hp1 φ z) := by
  have hlocal : (sourceComplexAction hp hp1 n) =ᶠ[𝓝 φ]
      (fun ψ : CoeffPair p =>
        sourceActionCircle hp hp1 ψ
          ch.spectralCenter ch.spectralRadius) := by
    filter_upwards [isOpen_ball.mem_nhds hφch] with ψ hψ
    exact sourceComplexAction_eq_chart hp hp1 n ch ψ hψ
  have hgeom := ch.geometry φ hφch
  have hcircle : sphere ch.spectralCenter ch.spectralRadius ⊆
      sourceCanonicalRootDomain hp hp1 φ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n
      ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  rw [hlocal.fderiv_eq]
  exact fderiv_sourceActionCircle_eq_gradient_integral
    hp hp1 φ hφ ch.spectralCenter ch.spectralRadius
    ch.spectralRadius_pos hcircle h

/-- At every real-type source and index, one isolating circle gives
the contour gradient formula in every complex source direction. -/
theorem exists_sourceComplexAction_gradient_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sourcePeriodicSegment hp hp1 φ n ⊆ ball c R ∧
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ n ∧
      ∀ h : CoeffPair p,
        (fderiv ℂ (sourceComplexAction hp hp1 n) φ) h =
          -(Real.pi : ℂ)⁻¹ *
            (∮ z in C(c,R),
              (fderiv ℂ (fun ψ : CoeffPair p =>
                canonicalDiscriminant hp (periodOnePotential ψ) z) φ) h /
                sourceCanonicalRoot hp hp1 φ z) := by
  obtain ⟨ch,hcenter⟩ :=
    exists_sourceRealActionBallChart_centered hp hp1 n φ hφ
  have hφch : φ ∈ ball ch.center ch.radius := by
    rw [hcenter]
    exact mem_ball_self ch.radius_pos
  have hgeom := ch.geometry φ hφch
  refine ⟨ch.spectralCenter,ch.spectralRadius,ch.spectralRadius_pos,
    hgeom.1,hgeom.2,?_⟩
  intro h
  exact fderiv_sourceComplexAction_eq_gradient_on_chart
    hp hp1 n ch φ hφ hφch h

end NLS.ZakharovShabat
