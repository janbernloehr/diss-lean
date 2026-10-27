import NLS.ZakharovShabat.PhysicalParitySelfAdjoint
import NLS.ZakharovShabat.PeriodicSelfAdjointRealType

/-! # Real-type necessity from either separate parity operator -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

/-- Testing two same-parity modes recovers every allowed potential coefficient. -/
theorem isRealType_of_parity_domainPairing_operator_conj {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (r : ℤ)
    (h : ∀ a ∈ domainParitySubspace (p := p) r, ∀ b ∈ domainParitySubspace (p := p) r,
      domainPairing hp (operator hp φ a) b = conj (domainPairing hp (operator hp φ b) a)) :
    IsRealType φ := by
  intro n
  by_cases hn : n%2 = 0
  · have hb : positiveMode (p := p) (n-r) ∈ domainParitySubspace r := by
      intro k hk
      exact positiveMode_mem_domainParitySubspace (n-r) k (by omega)
    have hh := h (negativeMode r) (negativeMode_mem_domainParitySubspace r) (positiveMode (n-r)) hb
    simpa [domainPairing,Coeff.pairing,negativeMode,positiveMode,
      operator_fst_apply,operator_snd_apply,mul_ite,ite_mul,
      show -r-(n-r) = -n by ring] using hh
  · have hf : φ.1 (-n) = 0 := (Coeff.mem_paritySubspace 0 φ.1).mp hφ.1 (-n) (by omega)
    have hs : φ.2 n = 0 := (Coeff.mem_paritySubspace 0 φ.2).mp hφ.2 n (by simpa using hn)
    rw [hf,hs,map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Symmetry on either original source parity domain already forces real type. -/
theorem isRealType_of_sourceParityOperator_inner_symmetric (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ)
    (h : ∀ a b : sourceDomainParitySubspace (p := 2) r,
      inner ℂ (sourceParityOperator (by simp) φ hφ r a) (sourceParityDomainInclusion r b) =
      inner ℂ (sourceParityDomainInclusion r a) (sourceParityOperator (by simp) φ hφ r b)) :
    IsRealType (CoeffPair.toMax 2 φ) := by
  apply isRealType_of_parity_domainPairing_operator_conj (by simp) (CoeffPair.toMax 2 φ) hφ r
  intro a ha b hb
  let A : sourceDomainParitySubspace (p := 2) r :=
    ⟨(WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm a,by
      change (WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
        ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm a) ∈ domainParitySubspace r
      rwa [ContinuousLinearEquiv.apply_symm_apply]⟩
  let B : sourceDomainParitySubspace (p := 2) r :=
    ⟨(WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm b,by
      change (WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
        ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm b) ∈ domainParitySubspace r
      rwa [ContinuousLinearEquiv.apply_symm_apply]⟩
  have hh := h B A
  simp only [Submodule.coe_inner,sourceParityOperator_coe,sourceParityDomainInclusion_coe] at hh
  rw [← inner_conj_symm,sourceDomainInclusion_inner,sourceDomainInclusion_inner] at hh
  simp only [A,B,sourceOperator,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] at hh
  exact hh.symm

/-- For each individual sector, equality with the Hilbert adjoint characterizes real type. -/
theorem sourceParityUnboundedOperator_isSelfAdjoint_iff (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) :
    IsSelfAdjoint (sourceParityUnboundedOperator (by simp) φ hφ r) ↔
      IsRealType (CoeffPair.toMax 2 φ) := by
  refine ⟨fun h => ?_,fun h => sourceParityUnboundedOperator_isSelfAdjoint φ hφ h r⟩
  apply isRealType_of_sourceParityOperator_inner_symmetric φ hφ r
  have hs : (sourceParityUnboundedOperator (by simp) φ hφ r).IsFormalAdjoint
      (sourceParityUnboundedOperator (by simp) φ hφ r) := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp h] using
      LinearPMap.adjoint_isFormalAdjoint h.dense_domain
  intro a b
  simpa only [sourceParityUnboundedOperator_apply,sourceParityUnboundedDomainEquiv_coe] using
    hs (sourceParityUnboundedDomainEquiv r a) (sourceParityUnboundedDomainEquiv r b)

/-- The original physical expression on either parity space has the same exact characterization. -/
theorem physicalParityOperator_isSelfAdjoint_iff (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) :
    IsSelfAdjoint (physicalParityOperator φ hφ r) ↔ IsRealType (CoeffPair.toMax 2 φ) := by
  refine ⟨fun h => ?_,fun h => physicalParityOperator_isSelfAdjoint φ hφ h r⟩
  apply isRealType_of_sourceParityOperator_inner_symmetric φ hφ r
  have hs : (physicalParityOperator φ hφ r).IsFormalAdjoint (physicalParityOperator φ hφ r) := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp h] using
      LinearPMap.adjoint_isFormalAdjoint h.dense_domain
  intro a b
  simpa only [physicalParityOperator_apply,physicalParityDomainEquiv_coe,
    (sourceParityCircleSynthesis r).inner_map_map] using
    hs (physicalParityDomainEquiv r a) (physicalParityDomainEquiv r b)

/-- Each boundary sector of an original period-one potential is self-adjoint exactly for real type. -/
theorem sourcePhysicalParityOperator_isSelfAdjoint_iff (φ : CoeffPair 2) (r : ℤ) :
    IsSelfAdjoint (physicalParityOperator (periodOnePair φ) (periodOnePotential_mem φ) r) ↔
      IsRealType (CoeffPair.toMax 2 φ) := by
  exact (physicalParityOperator_isSelfAdjoint_iff (periodOnePair φ)
    (periodOnePotential_mem φ) r).trans (isRealType_periodOnePotential_iff φ)

end NLS.ZakharovShabat
