import NLS.Poisson.SourceHamiltonianDirection
import NLS.ZakharovShabat.SourceBoundaryIsospectralAction
import NLS.ZakharovShabat.SourceCanonicalRootSourceFDeriv

/-! # Actual isospectral source directions

An isospectral direction annihilates the actual discriminant cotangent
at every spectral parameter. The actual canonical square root then has
zero variation off its periodic cuts. The actual action Hamiltonian
directions are isospectral by the proved action/discriminant bracket.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Infinitesimal isospectrality refers to the actual discriminant,
not an assumed deformation of auxiliary spectral data. -/
def SourceIsospectralDirection (hp : p ≠ ⊤) (φ h : CoeffPair p) : Prop :=
  ∀ z : ℂ, (sourceDiscriminantCotangent hp z φ) h = 0

/-- The actual square root has zero source variation in every
isospectral direction, wherever the spectral parameter avoids its cuts. -/
theorem fderiv_sourceCanonicalRoot_eq_zero_of_isospectralDirection
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (h : CoeffPair p)
    (hiso : SourceIsospectralDirection hp φ h)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourceCanonicalRoot hp hp1 ψ z) φ) h = 0 := by
  rw [fderiv_sourceCanonicalRoot_eq_discriminant_div_root_mul_fderiv hp hp1 φ hreal z hz]
  change canonicalDiscriminant hp (periodOnePotential φ) z/sourceCanonicalRoot hp hp1 φ z*
    (sourceDiscriminantCotangent hp z φ) h = 0
  rw [hiso z,mul_zero]

/-- Every actual indexed action defines an actual isospectral source
direction at each real-type source for finite exponents at least two. -/
theorem sourceHamiltonianVector_action_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (m : ℤ) :
    SourceIsospectralDirection hp φ
      (sourceHamiltonianVector h2p (sourceComplexAction hp hp1 m) φ) := by
  intro z
  rw [sourceDiscriminantCotangent,fderiv_apply_sourceHamiltonianVector]
  exact sourceBracket_discriminant_action_eq_zero hp hp1 h2p φ hreal z m

/-- The fixed-parameter canonical square root is stationary under
every actual action Hamiltonian direction, off the periodic cuts. -/
theorem fderiv_sourceCanonicalRoot_sourceHamiltonianVector_action_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (m : ℤ) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourceCanonicalRoot hp hp1 ψ z) φ)
      (sourceHamiltonianVector h2p (sourceComplexAction hp hp1 m) φ) = 0 :=
  fderiv_sourceCanonicalRoot_eq_zero_of_isospectralDirection hp hp1 φ hreal _
    (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ hreal m) z hz

end NLS.ZakharovShabat
