import NLS.ZakharovShabat.ClassicalCanonicalIdentity

/-!
# Classical representatives of domain-valued potentials

The continuous Sobolev representative of an original domain element supplies
exactly the compatibility hypothesis needed by the classical product identity.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The unit-interval domain curve represents the included Hilbert potential. -/
theorem physicalBase_eq_extend_physicalDomainCurve (a : Domain 2) :
    physicalBase (domainInclusion a) =ᵐ[volume.restrict (Ioc 0 1)] extend (physicalDomainCurve a) := by
  have h := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num)) (physicalBase_domainInclusion a)
  filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with t ht hmem
  rw [ht]
  simp [NLS.LinearVolterra.extend, projIcc_of_mem _ (Ioc_subset_Icc_self hmem), physicalDomainCurve]

/-- Every even domain potential has the exact classical parity normalization. -/
theorem canonicalParity_domainInclusion_eq_classical (a : Domain 2)
    (ha : a ∈ domainParitySubspace 0) (k : ℤ) (hk : k = 0 ∨ k = 1) (z : ℂ) :
    canonicalParityProduct (by simp) (domainInclusion a) k z =
      classicalDiscriminant (physicalDomainCurve a) z-2*NLS.Fourier.wave k 1 :=
  canonicalParity_eq_classical (domainInclusion a) ((mem_domainParitySubspace 0 a).mp ha)
    (physicalDomainCurve a) (physicalBase_eq_extend_physicalDomainCurve a) k hk z

/-- The shifted-product identity needs no separate representative hypothesis on the domain. -/
theorem canonicalParity_shifted_eq_domainInclusion (a : Domain 2)
    (ha : a ∈ domainParitySubspace 0) (z : ℂ) :
    canonicalParityProduct (by simp) (domainInclusion a) 0 z+2 =
      canonicalParityProduct (by simp) (domainInclusion a) 1 z-2 := by
  obtain ⟨he, ho⟩ := canonicalParity_shifted_eq_classical (domainInclusion a)
    ((mem_domainParitySubspace 0 a).mp ha) (physicalDomainCurve a)
    (physicalBase_eq_extend_physicalDomainCurve a) z
  exact he.trans ho.symm

end NLS.ZakharovShabat
