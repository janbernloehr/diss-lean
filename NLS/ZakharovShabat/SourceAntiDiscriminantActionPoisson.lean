import NLS.ZakharovShabat.SourceAntiDiscriminantPoisson
import NLS.ZakharovShabat.SourceBoundaryRootActionPoisson

/-! # Actual anti-discriminant/action contour kernels

The actual action cotangent circle formula represents a fixed-parameter
anti-discriminant/action bracket by the proved anti-discriminant/discriminant
flow. At a canonical boundary root, real interlacing makes the spectral
difference nonzero on every admissible action circle. The Dirichlet and
Neumann zero equations then give their opposite signed kernels.
The selected base root is held fixed in the anti-discriminant functional.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual fixed-spectral anti-discriminant/action bracket is the
single contour integral of its entire discriminant bracket. -/
theorem sourceBracket_anti_action_eq_discriminant_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (z : ℂ) (m : ℤ) (ch : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    sourceBracket h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z)
      (sourceComplexAction hp hp1 m) φ =
        -(Real.pi : ℂ)⁻¹*
          (∮ w in C(ch.spectralCenter,ch.spectralRadius),
            (sourceCanonicalRoot hp hp1 φ w)⁻¹*sourceBracket h2p
              (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z)
              (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ) := by
  have hgeom := ch.geometry φ hφ
  have hcircle := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m
    ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  have hint := circleIntegrable_sourceActionVariationCotangent hp hp1 φ
    ch.spectralCenter ch.spectralRadius ch.spectralRadius_pos.le hcircle
  rw [sourceBracket,fderiv_sourceComplexAction_eq_cotangent_circle_on_chart hp hp1 m ch φ hreal hφ]
  simp only [map_smul,smul_eq_mul]
  rw [NLS.ComplexAnalysis.map_circleIntegral
    (sourceBivector h2p (fderiv ℂ (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z) φ)) hint]
  congr 1
  apply circleIntegral.integral_congr ch.spectralRadius_pos.le
  intro w _
  dsimp only
  simp only [sourceActionVariationCotangent,sourceDiscriminantCotangent,
    sourceBracket,map_smul,smul_eq_mul]

/-- When the fixed spectral point avoids the action circle, the literal
characteristic determinant quotient is the actual action integrand. -/
theorem sourceBracket_anti_action_eq_characteristic_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (z : ℂ) (m : ℤ) (ch : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius)
    (havoid : ∀ w ∈ sphere ch.spectralCenter ch.spectralRadius, z ≠ w) :
    sourceBracket h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z)
      (sourceComplexAction hp hp1 m) φ =
        -(Real.pi : ℂ)⁻¹*
          (∮ w in C(ch.spectralCenter,ch.spectralRadius),
            (sourceCanonicalRoot hp hp1 φ w)⁻¹*
              (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z*periodOneBoundaryCharacteristic hp hp1 .neumann φ w-
                periodOneBoundaryCharacteristic hp hp1 .neumann φ z*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w)/(z-w)) := by
  rw [sourceBracket_anti_action_eq_discriminant_circle hp hp1 h2p z m ch φ hreal hφ]
  congr 1
  apply circleIntegral.integral_congr ch.spectralRadius_pos.le
  intro w hw
  dsimp only
  rw [sourceBracket_anti_discriminant_eq hp hp1 h2p φ z w (havoid w hw)]
  ring

/-- At an actual canonical Dirichlet root, held fixed in the first
functional, the action kernel has the positive Neumann prefactor. -/
theorem sourceBracket_anti_action_at_canonicalDirichletRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n m : ℤ) (ch : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
    sourceBracket h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ μ)
      (sourceComplexAction hp hp1 m) φ =
        (Real.pi : ℂ)⁻¹*periodOneBoundaryCharacteristic hp hp1 .neumann φ μ*
          (∮ w in C(ch.spectralCenter,ch.spectralRadius),
            (sourceCanonicalRoot hp hp1 φ w)⁻¹*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w/(μ-w)) := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n
  have hgeom := ch.geometry φ hφ
  have hcircle := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m
    ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  have havoid : ∀ w ∈ sphere ch.spectralCenter ch.spectralRadius, μ ≠ w :=
    fun w hw => canonicalPeriodOneBoundaryRoot_ne_of_sourceCanonicalRootDomain hp hp1 .dirichlet φ hreal n w (hcircle hw)
  change sourceBracket h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ μ)
    (sourceComplexAction hp hp1 m) φ = _
  rw [sourceBracket_anti_action_eq_characteristic_circle hp hp1 h2p μ m ch φ hreal hφ havoid]
  have hz : periodOneBoundaryCharacteristic hp hp1 .dirichlet φ μ = 0 :=
    periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 .dirichlet φ n
  rw [hz]
  have heq : (∮ w in C(ch.spectralCenter,ch.spectralRadius),
      (sourceCanonicalRoot hp hp1 φ w)⁻¹*
        (0*periodOneBoundaryCharacteristic hp hp1 .neumann φ w-
          periodOneBoundaryCharacteristic hp hp1 .neumann φ μ*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w)/(μ-w)) =
      -periodOneBoundaryCharacteristic hp hp1 .neumann φ μ*
        (∮ w in C(ch.spectralCenter,ch.spectralRadius),
          (sourceCanonicalRoot hp hp1 φ w)⁻¹*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w/(μ-w)) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr ch.spectralRadius_pos.le
    intro w _
    dsimp only
    ring
  rw [heq]
  ring

/-- At an actual canonical Neumann root, held fixed in the first
functional, the action kernel has the negative Dirichlet prefactor. -/
theorem sourceBracket_anti_action_at_canonicalNeumannRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n m : ℤ) (ch : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    let ν := canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n
    sourceBracket h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ ν)
      (sourceComplexAction hp hp1 m) φ =
        -(Real.pi : ℂ)⁻¹*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ ν*
          (∮ w in C(ch.spectralCenter,ch.spectralRadius),
            (sourceCanonicalRoot hp hp1 φ w)⁻¹*periodOneBoundaryCharacteristic hp hp1 .neumann φ w/(ν-w)) := by
  let ν := canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n
  have hgeom := ch.geometry φ hφ
  have hcircle := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m
    ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  have havoid : ∀ w ∈ sphere ch.spectralCenter ch.spectralRadius, ν ≠ w :=
    fun w hw => canonicalPeriodOneBoundaryRoot_ne_of_sourceCanonicalRootDomain hp hp1 .neumann φ hreal n w (hcircle hw)
  change sourceBracket h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ ν)
    (sourceComplexAction hp hp1 m) φ = _
  rw [sourceBracket_anti_action_eq_characteristic_circle hp hp1 h2p ν m ch φ hreal hφ havoid]
  have hz : periodOneBoundaryCharacteristic hp hp1 .neumann φ ν = 0 :=
    periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 .neumann φ n
  rw [hz]
  have heq : (∮ w in C(ch.spectralCenter,ch.spectralRadius),
      (sourceCanonicalRoot hp hp1 φ w)⁻¹*
        (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ ν*periodOneBoundaryCharacteristic hp hp1 .neumann φ w-
          0*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w)/(ν-w)) =
      periodOneBoundaryCharacteristic hp hp1 .dirichlet φ ν*
        (∮ w in C(ch.spectralCenter,ch.spectralRadius),
          (sourceCanonicalRoot hp hp1 φ w)⁻¹*periodOneBoundaryCharacteristic hp hp1 .neumann φ w/(ν-w)) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr ch.spectralRadius_pos.le
    intro w _
    dsimp only
    ring
  rw [heq]
  ring

end NLS.ZakharovShabat
