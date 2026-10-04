import NLS.ZakharovShabat.SourceFullAbelianDifferentialData
import NLS.ZakharovShabat.SourceAngularThetaDiscriminant

/-! # Angle brackets of the actual full primitive

The exact primitive differential and the established theta/discriminant
identity give the psi quotient with its original sign and factor.
The chain rule then gives the cubic bracket used in Lemma 20.2.
-/
noncomputable section
open Set Metric Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAngularThetaCommonDomainData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B V W U : Set (CoeffPair p)} {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The angle bracket of every normalization of the primitive is
minus one half of the actual normalized psi quotient. -/
theorem thetaFullPrimitive_eq
    (E : SourceAngularThetaCommonDomainData hp hp1 W₀ B V s)
    (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n j : ℤ) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ U)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s
      (fun ψ => sourceFullAbelianPrimitive hp hp1 W j (z,ψ)) φ.val =
      -(1/2 : ℂ)*sourcePsiContourIntegrandJoint hp hp1 n (z,((s n φ.val : Coeff p),φ.val)) := by
  have he := E.thetaDiscriminant_eq h2p n φ hgap z
  change sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s φ.val)
    (sourceDiscriminantCotangent hp z φ.val) = _ at he
  unfold sourceAngularThetaFunctionalBracket
  rw [D.source_fderiv j z φ.val hφ hz]
  simp only [map_smul,smul_eq_mul]
  rw [he]
  dsimp [sourcePsiContourIntegrandJoint]
  ring

/-- The power chain rule with the actual cotangents, at any positive order. -/
theorem thetaFullPrimitive_pow_eq
    (E : SourceAngularThetaCommonDomainData hp hp1 W₀ B V s)
    (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n j : ℤ) (m : ℕ) (φ : realTypeSourceLocus p)
    (hφ : φ.val ∈ U)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ.val) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s
      (fun ψ => (sourceFullAbelianPrimitive hp hp1 W j (z,ψ))^(m+1)) φ.val =
      -((m+1 : ℕ) : ℂ)/2*(sourceFullAbelianPrimitive hp hp1 W j (z,φ.val))^m*
        sourcePsiContourIntegrandJoint hp hp1 n (z,((s n φ.val : Coeff p),φ.val)) := by
  have he := E.thetaDiscriminant_eq h2p n φ hgap z
  change sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s φ.val)
    (sourceDiscriminantCotangent hp z φ.val) = _ at he
  have hd := (D.source_hasFDerivAt j z φ.val hφ hz).pow (m+1)
  unfold sourceAngularThetaFunctionalBracket
  rw [hd.fderiv]
  simp only [Nat.add_sub_cancel_right,map_smul,smul_eq_mul]
  rw [he]
  dsimp [sourcePsiContourIntegrandJoint]
  simp only [Nat.cast_add,Nat.cast_one,nsmul_eq_mul]
  ring

end NLS.ZakharovShabat.SourceAngularThetaCommonDomainData
