import NLS.ZakharovShabat.SourceBoundarySpectralCurveDifferential

/-! # Actual action Hamiltonians preserve the separation spectral curve

The actual indexed actions commute with every fixed-parameter
discriminant. Passing the proved full separation cotangent equation
through the source bivector gives the tangent equation for every
isospectral Hamiltonian, in particular for every actual action.
Only the final quotient formula excludes a vanishing terminal square root.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual action is isospectral at every real source. The action
cotangent is its proved contour integral of discriminant cotangents. -/
theorem sourceBracket_discriminant_action_eq_zero_on_chart
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (z : ℂ) (m : ℤ) (ch : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z)
      (sourceComplexAction hp hp1 m) φ = 0 := by
  have hgeom := ch.geometry φ hφ
  have hcircle := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m
    ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  have hint := circleIntegrable_sourceActionVariationCotangent hp hp1 φ
    ch.spectralCenter ch.spectralRadius ch.spectralRadius_pos.le hcircle
  unfold sourceBracket
  rw [fderiv_sourceComplexAction_eq_cotangent_circle_on_chart hp hp1 m ch φ hreal hφ]
  simp only [map_smul,smul_eq_mul]
  rw [NLS.ComplexAnalysis.map_circleIntegral
    (sourceBivector h2p (fderiv ℂ
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ)) hint]
  have hzero : (∮ w in C(ch.spectralCenter,ch.spectralRadius),
      sourceBivector h2p (fderiv ℂ
        (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ)
        (sourceActionVariationCotangent hp hp1 φ w)) = 0 := by
    calc
      _ = ∮ w in C(ch.spectralCenter,ch.spectralRadius), (0 : ℂ) := by
        apply circleIntegral.integral_congr ch.spectralRadius_pos.le
        intro w _
        simp only [sourceActionVariationCotangent,map_smul,smul_eq_mul]
        change (sourceCanonicalRoot hp hp1 φ w)⁻¹*sourceBracket h2p
          (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z)
          (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ = 0
        rw [sourceBracket_discriminants_eq_zero hp hp1 h2p φ,mul_zero]
      _ = 0 := by simp [circleIntegral]
  rw [hzero,mul_zero]

/-- No action chart, open gap, finite support, or spectral avoidance is
an extra hypothesis in the actual isospectral action identity. -/
theorem sourceBracket_discriminant_action_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (z : ℂ) (m : ℤ) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z)
      (sourceComplexAction hp hp1 m) φ = 0 := by
  obtain ⟨ch,hch⟩ := exists_sourceRealActionBallChart_centered hp hp1 m φ hreal
  exact sourceBracket_discriminant_action_eq_zero_on_chart hp hp1 h2p z m ch φ hreal
    (by rw [hch]; exact mem_ball_self ch.radius_pos)

/-- The actual separation point moves tangentially to its spectral curve
under any isospectral Hamiltonian. The cleared identity includes branch
terminals and collapsed gaps. -/
theorem sourceBracket_boundaryCanonicalMomentum_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (G : CoeffPair p → ℂ)
    (hiso : ∀ z : ℂ, sourceBracket h2p
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) G φ = 0) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    (extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ)*
      sourceBracket h2p (sourceBoundaryCanonicalMomentumAt hp hp1 b n φ) G φ+
      2*deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*
        sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) G φ = 0 := by
  dsimp only
  rw [sourceBracket_boundaryCanonicalMomentum_spectralCurve hp hp1 h2p b n φ hreal,hiso,zero_add]
  ring

/-- Every actual indexed action gives the cleared tangent equation for
the actual moving root and canonically normalized local momentum. -/
theorem sourceBracket_boundaryCanonicalMomentum_action_spectralCurve
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n m : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    (extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ)*
      sourceBracket h2p (sourceBoundaryCanonicalMomentumAt hp hp1 b n φ) (sourceComplexAction hp hp1 m) φ+
      2*deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*
        sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
          (sourceComplexAction hp hp1 m) φ = 0 :=
  sourceBracket_boundaryCanonicalMomentum_isospectral hp hp1 h2p b n φ hreal
    (sourceComplexAction hp hp1 m) (fun z => sourceBracket_discriminant_action_eq_zero hp hp1 h2p φ hreal z m)

/-- Away from a branch terminal, the action bracket of the actual local
momentum is the root bracket times the spectral logarithm weight. -/
theorem sourceBracket_boundaryCanonicalMomentum_action_eq_root_weight
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n m : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ))
    (hδ : sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ ≠ 0) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    sourceBracket h2p (sourceBoundaryCanonicalMomentumAt hp hp1 b n φ) (sourceComplexAction hp hp1 m) φ =
      (-2*deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*
        sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
          (sourceComplexAction hp hp1 m) φ)/
        (extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ) := by
  dsimp only
  have hsign : extensionSign b ≠ 0 := by cases b <;> norm_num [extensionSign]
  apply (eq_div_iff (mul_ne_zero hsign hδ)).mpr
  have h := sourceBracket_boundaryCanonicalMomentum_action_spectralCurve hp hp1 h2p b n m φ hreal
  dsimp only at h
  linear_combination h

end NLS.ZakharovShabat
