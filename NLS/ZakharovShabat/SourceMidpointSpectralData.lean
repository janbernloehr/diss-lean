import NLS.ZakharovShabat.SourceDiscriminantSpectralTransport
import NLS.ZakharovShabat.SourceMidpointReflection

/-! # Original labels and canonical-root signs under pure midpoint reflection

The combined P*T reflection preserves the discriminant, hence preserves every
intrinsic endpoint. Applying P afterwards gives the pure T endpoint and root
identities with their exact negative spectral sign, including all collisions.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceCanonicalPeriodicEndpoints_spatialReflection_complex (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceSpatialReflection φ)) (periodOnePotential_mem _) =
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential (sourceSpatialReflection φ)) (periodOnePotential_mem _) =
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) :=
  sourceCanonicalPeriodicEndpoints_eq_of_discriminant_eq hp hp1 (sourceSpatialReflection φ) φ
    (sourceDiscriminant_spatialReflection hp hp1 φ)

theorem sourceCanonicalPeriodicEndpoints_midpointReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceMidpointReflection φ)) (periodOnePotential_mem _) n =
      -canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential (sourceMidpointReflection φ)) (periodOnePotential_mem _) n =
      -canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n) := by
  have h := sourceCanonicalPeriodicEndpoints_componentSwap hp hp1 (sourceSpatialReflection φ) n
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_spatialReflection_complex hp hp1 φ
  simpa only [sourceMidpointReflection,LinearIsometryEquiv.trans_apply,hl,hr] using h

theorem sourceCanonicalRoot_spatialReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceCanonicalRoot hp hp1 (sourceSpatialReflection φ) z = sourceCanonicalRoot hp hp1 φ z :=
  sourceCanonicalRoot_eq_of_discriminant_eq hp hp1 (sourceSpatialReflection φ) φ
    (sourceDiscriminant_spatialReflection hp hp1 φ) z

theorem sourceCanonicalRoot_midpointReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) :
    sourceCanonicalRoot hp hp1 (sourceMidpointReflection φ) (-z) = -sourceCanonicalRoot hp hp1 φ z := by
  change sourceCanonicalRoot hp hp1 (sourceComponentSwap (sourceSpatialReflection φ)) (-z) = _
  rw [sourceCanonicalRoot_componentSwap hp hp1,sourceCanonicalRoot_spatialReflection hp hp1]

end NLS.ZakharovShabat
