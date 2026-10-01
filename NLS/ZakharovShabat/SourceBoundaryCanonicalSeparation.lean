import NLS.ZakharovShabat.SourceBoundaryFloquetCommutation

/-! # Canonically normalized actual separation functionals

The original period-one mixed root/Floquet logarithm bracket is minus
one half. Multiplying the actual local logarithm by minus two gives the
canonical mixed value one. The root and momentum functionals are analytic
locally, commute within each family, and satisfy all three canonical
separation bracket relations. No local inverse or action-angle claim is made.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual local logarithmic momentum with the canonical bracket
normalization fixed by the original period-one source bivector. -/
def sourceBoundaryCanonicalMomentumAt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (n : ℤ) (φ ψ : CoeffPair p) : ℂ :=
  -2*sourceBoundaryFloquetLogAt hp hp1 b n φ ψ

@[simp] theorem sourceBoundaryCanonicalMomentumAt_self
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p) :
    sourceBoundaryCanonicalMomentumAt hp hp1 b n φ φ = 0 := by
  simp [sourceBoundaryCanonicalMomentumAt]

theorem analyticAt_sourceBoundaryCanonicalMomentumAt_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticAt ℂ (sourceBoundaryCanonicalMomentumAt hp hp1 b n φ) φ :=
  analyticAt_const.mul (analyticAt_sourceBoundaryFloquetLogAt_of_realType hp hp1 b n φ hreal)

theorem fderiv_sourceBoundaryCanonicalMomentumAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    fderiv ℂ (sourceBoundaryCanonicalMomentumAt hp hp1 b n φ) φ =
      (-2 : ℂ) • fderiv ℂ (sourceBoundaryFloquetLogAt hp hp1 b n φ) φ :=
  fderiv_const_mul (analyticAt_sourceBoundaryFloquetLogAt_of_realType hp hp1 b n φ hreal).differentiableAt (-2 : ℂ)

/-- All actual normalized local separation momenta commute within each
ordinary boundary family, with no open-gap or branch hypothesis. -/
theorem sourceBracket_boundaryCanonicalMomenta_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    sourceBracket h2p (sourceBoundaryCanonicalMomentumAt hp hp1 b n φ)
      (sourceBoundaryCanonicalMomentumAt hp hp1 b m φ) φ = 0 := by
  unfold sourceBracket
  rw [fderiv_sourceBoundaryCanonicalMomentumAt hp hp1 b n φ hreal,
    fderiv_sourceBoundaryCanonicalMomentumAt hp hp1 b m φ hreal]
  simp only [map_smul,smul_apply,smul_eq_mul]
  change (-2 : ℂ)*((-2 : ℂ)*sourceBracket h2p (sourceBoundaryFloquetLogAt hp hp1 b n φ)
    (sourceBoundaryFloquetLogAt hp hp1 b m φ) φ) = 0
  rw [sourceBracket_boundaryFloquetLogs_eq_zero hp hp1 h2p b φ hreal]
  simp

/-- The actual mixed canonical separation bracket equals the Kronecker
delta for all indexed roots, including those on collapsed gaps. -/
theorem sourceBracket_boundaryRoot_canonicalMomentum_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (sourceBoundaryCanonicalMomentumAt hp hp1 b m φ) φ = if n = m then 1 else 0 := by
  unfold sourceBracket
  rw [fderiv_sourceBoundaryCanonicalMomentumAt hp hp1 b m φ hreal]
  simp only [map_smul,smul_eq_mul]
  change (-2 : ℂ)*sourceBracket h2p
    (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
    (sourceBoundaryFloquetLogAt hp hp1 b m φ) φ = _
  rw [sourceBracket_boundaryRoot_floquetLog_eq hp hp1 h2p b φ hreal]
  by_cases hnm : n = m <;> norm_num [hnm]

/-- All three actual canonical separation relations hold simultaneously
within either ordinary boundary family at every real-type source for
finite p at least two. This is a bracket theorem, not an inverse theorem. -/
theorem sourceBoundaryCanonicalSeparation_relations
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) φ = 0 ∧
    sourceBracket h2p (sourceBoundaryCanonicalMomentumAt hp hp1 b n φ)
      (sourceBoundaryCanonicalMomentumAt hp hp1 b m φ) φ = 0 ∧
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (sourceBoundaryCanonicalMomentumAt hp hp1 b m φ) φ = if n = m then 1 else 0 :=
  ⟨sourceBracket_boundaryRoots_eq_zero hp hp1 h2p b φ hreal n m,
    sourceBracket_boundaryCanonicalMomenta_eq_zero hp hp1 h2p b φ hreal n m,
    sourceBracket_boundaryRoot_canonicalMomentum_eq hp hp1 h2p b φ hreal n m⟩

end NLS.ZakharovShabat
