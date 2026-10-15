import NLS.ZakharovShabat.SourceSobolevAngleVector
import NLS.ZakharovShabat.SourceSobolevHamiltonianDifferential

/-! # The physical H¹ energy bracket along the recovered angle vector

The bracket applies the full physical H¹ energy differential to the
constructed H¹ angle vector, with the original negative sign. Whenever
that vector has the original Hamiltonian coefficients, every Hilbert
cotangent representing the physical energy differential gives precisely
the original Poisson bivector. An L² energy cotangent is not assumed to
exist at an arbitrary H¹ source.
-/
noncomputable section
open Set Filter Topology Complex NLS.Poisson
namespace NLS.ZakharovShabat

/-- The physical energy derivative along the recovered H¹ angle direction. -/
def sourceSobolevThetaEnergyBracket (n : ℤ)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (a : ScalarDomain 2 × ScalarDomain 2) : ℂ :=
  -(fderiv ℂ periodOneSobolevHamiltonian a (sourceSobolevThetaVector n s a))

/-- Any H¹ lift of the original Hamiltonian coefficients gives the same physical bracket. -/
theorem sourceSobolevThetaEnergyBracket_eq_of_lift (n : ℤ)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (a v : ScalarDomain 2 × ScalarDomain 2)
    (ha : sobolevSourceInclusion (sourceSobolevThetaVector n s a) =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a))
    (hv : sobolevSourceInclusion v =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a)) :
    sourceSobolevThetaEnergyBracket n s a = -(fderiv ℂ periodOneSobolevHamiltonian a v) := by
  rw [sourceSobolevThetaEnergyBracket,sobolevSourceInclusion_injective (ha.trans hv.symm)]

/-- The physical H¹ directional bracket agrees with the original bivector
whenever the energy differential has a Hilbert cotangent representative. -/
theorem sourceSobolevThetaEnergyBracket_eq_sourceBivector (n : ℤ)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : sobolevSourceInclusion (sourceSobolevThetaVector n s a) =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a))
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : fderiv ℂ periodOneSobolevHamiltonian a = L.comp sobolevSourceInclusion) :
    sourceSobolevThetaEnergyBracket n s a = sourceBivector le_rfl
      (sourceAngularThetaDifferential (by simp) (by norm_num) n s (sobolevSourceInclusion a)) L := by
  rw [sourceSobolevThetaEnergyBracket,hL,ContinuousLinearMap.comp_apply,ha,
    sourceAngularThetaHamiltonianVector,apply_sourceHamiltonianDirection,sourceBivector_antisymm,neg_neg]

/-- Analyticity follows from the full physical energy differential and bounded H¹ recovery. -/
theorem analyticAt_sourceSobolevThetaEnergyBracket
    {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) W₀ B W s)
    (n : ℤ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ W)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0) :
    AnalyticAt ℂ (sourceSobolevThetaEnergyBracket n s) a :=
  (((ContinuousLinearMap.id ℂ ((ScalarDomain 2 × ScalarDomain 2) →L[ℂ] ℂ)).analyticAt_bilinear _).comp₂
    (analyticAt_periodOneSobolevHamiltonian a).fderiv
    (analyticAt_sourceSobolevThetaVector E n a ha hn)).neg

end NLS.ZakharovShabat
