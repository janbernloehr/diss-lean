import NLS.ZakharovShabat.SourceBoundaryRootPoisson
import NLS.ZakharovShabat.SourceAngularBetaRegularAnalytic

/-! # Actual boundary-root/action brackets

The proved action cotangent circle formula gives a single spectral
integral of the actual moving-root/discriminant bracket. The actual
root lies on its periodic segment at real type, so every admissible
action circle avoids it. The literal characteristic quotient therefore
gives the signed root/action kernel on every indexed action chart.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every spectral point outside the periodic segments differs from every
actual real-source boundary root, including roots on collapsed segments. -/
theorem canonicalPeriodOneBoundaryRoot_ne_of_sourceCanonicalRootDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (w : ℂ) (hw : w ∈ sourceCanonicalRootDomain hp hp1 φ) :
    canonicalPeriodOneBoundaryRoots hp hp1 b φ n ≠ w := by
  intro heq
  apply hw n
  rw [← heq]
  exact canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1 b φ hreal n

/-- The actual indexed boundary-root/action bracket is a single contour
integral of the entire moving-root/discriminant bracket. -/
theorem sourceBracket_boundaryRoot_action_eq_discriminant_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n m : ℤ) (ch : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (sourceComplexAction hp hp1 m) φ =
        -(Real.pi : ℂ)⁻¹*
          (∮ w in C(ch.spectralCenter,ch.spectralRadius),
            (sourceCanonicalRoot hp hp1 φ w)⁻¹*sourceBoundaryRootDiscriminantBracket hp hp1 h2p b φ n w) := by
  have hgeom := ch.geometry φ hφ
  have hcircle := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m
    ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  have hint := circleIntegrable_sourceActionVariationCotangent hp hp1 φ
    ch.spectralCenter ch.spectralRadius ch.spectralRadius_pos.le hcircle
  rw [sourceBracket,fderiv_sourceComplexAction_eq_cotangent_circle_on_chart hp hp1 m ch φ hreal hφ]
  simp only [map_smul,smul_eq_mul]
  rw [NLS.ComplexAnalysis.map_circleIntegral
    (sourceBivector h2p (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ)) hint]
  congr 1
  apply circleIntegral.integral_congr ch.spectralRadius_pos.le
  intro w _
  dsimp only
  simp only [sourceActionVariationCotangent,sourceDiscriminantCotangent,
    sourceBoundaryRootDiscriminantBracket,sourceBracket,map_smul,smul_eq_mul]

/-- The actual characteristic quotient, divided by the canonical periodic
root, is the root/action spectral integrand on an admissible action circle. -/
theorem sourceBracket_boundaryRoot_action_eq_characteristic_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n m : ℤ) (ch : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (sourceComplexAction hp hp1 m) φ =
        -(Real.pi : ℂ)⁻¹*
          (∮ w in C(ch.spectralCenter,ch.spectralRadius),
            (sourceCanonicalRoot hp hp1 φ w)⁻¹*
              (extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ μ*
                periodOneBoundaryCharacteristic hp hp1 b φ w)/
                  (2*(μ-w)*deriv (periodOneBoundaryCharacteristic hp hp1 b φ) μ)) := by
  dsimp only
  rw [sourceBracket_boundaryRoot_action_eq_discriminant_circle hp hp1 h2p b n m ch φ hreal hφ]
  have hgeom := ch.geometry φ hφ
  have hcircle := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m
    ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  congr 1
  apply circleIntegral.integral_congr ch.spectralRadius_pos.le
  intro w hw
  dsimp only
  rw [sourceBoundaryRootDiscriminantBracket_eq hp hp1 h2p b φ hreal n w
    (canonicalPeriodOneBoundaryRoot_ne_of_sourceCanonicalRootDomain hp hp1 b φ hreal n w (hcircle hw))]
  ring

/-- At every real source and pair of indices there is an actual isolating
action circle with the proved characteristic kernel. Neither gap needs to
be open, and no finite-source or spectral bracket identity is assumed. -/
theorem exists_sourceBracket_boundaryRoot_action_characteristic_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    ∃ ch : SourceRealActionBallChart hp hp1 m,
      φ ∈ ball ch.center ch.radius ∧
      sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
        (sourceComplexAction hp hp1 m) φ =
          -(Real.pi : ℂ)⁻¹*
            (∮ w in C(ch.spectralCenter,ch.spectralRadius),
              (sourceCanonicalRoot hp hp1 φ w)⁻¹*
                (extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ
                    (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)*
                  periodOneBoundaryCharacteristic hp hp1 b φ w)/
                    (2*(canonicalPeriodOneBoundaryRoots hp hp1 b φ n-w)*
                      deriv (periodOneBoundaryCharacteristic hp hp1 b φ)
                        (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))) := by
  obtain ⟨ch,hcenter⟩ := exists_sourceRealActionBallChart_centered hp hp1 m φ hreal
  have hφ : φ ∈ ball ch.center ch.radius := by
    rw [hcenter]
    exact mem_ball_self ch.radius_pos
  exact ⟨ch,hφ,sourceBracket_boundaryRoot_action_eq_characteristic_circle hp hp1 h2p b n m ch φ hreal hφ⟩

/-- A boundary root in a collapsed periodic gap commutes with every actual
indexed action, regardless of whether the action's own gap is collapsed. -/
theorem sourceBracket_boundaryRoot_action_eq_zero_of_collapsed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (sourceComplexAction hp hp1 m) φ = 0 := by
  obtain ⟨ch,hcenter⟩ := exists_sourceRealActionBallChart_centered hp hp1 m φ hreal
  have hφ : φ ∈ ball ch.center ch.radius := by
    rw [hcenter]
    exact mem_ball_self ch.radius_pos
  rw [sourceBracket_boundaryRoot_action_eq_discriminant_circle hp hp1 h2p b n m ch φ hreal hφ]
  simp_rw [sourceBoundaryRootDiscriminantBracket_eq_zero_of_collapsed_gap hp hp1 h2p b φ hreal n hgap]
  simp [circleIntegral]

end NLS.ZakharovShabat
