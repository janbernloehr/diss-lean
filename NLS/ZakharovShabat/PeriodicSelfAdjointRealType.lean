import NLS.ZakharovShabat.PhysicalPeriodicSelfAdjoint

/-! # Periodic self-adjointness characterizes real-type potentials -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat

/-- Two signed Fourier modes recover the conjugate-reflection identity from operator symmetry. -/
theorem isRealType_of_domainPairing_operator_conj {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (φ : PairSpace p)
    (h : ∀ a b : Domain p, domainPairing hp (operator hp φ a) b =
      conj (domainPairing hp (operator hp φ b) a)) : IsRealType φ := by
  intro n
  have hh := h (negativeMode 0) (positiveMode n)
  simpa [domainPairing,Coeff.pairing,negativeMode,positiveMode,
    operator_fst_apply,operator_snd_apply,mul_ite,ite_mul] using hh

theorem isRealType_of_sourceOperator_inner_symmetric (φ : CoeffPair 2)
    (h : ∀ a b : WeightedCoeffPair (Weight.sobolev 1) 2,
      inner ℂ (sourceOperator (by simp) φ a) (sourceDomainInclusion b) =
      inner ℂ (sourceDomainInclusion a) (sourceOperator (by simp) φ b)) :
    IsRealType (CoeffPair.toMax 2 φ) := by
  apply isRealType_of_domainPairing_operator_conj (by simp)
  intro a b
  let A := (WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm a
  let B := (WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm b
  have hh := h B A
  rw [← inner_conj_symm,sourceDomainInclusion_inner,sourceDomainInclusion_inner] at hh
  simpa only [A,B,sourceOperator,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using hh.symm

/-- Exact adjoint equality holds if and only if the original source potential has real type. -/
theorem sourceUnboundedOperator_isSelfAdjoint_iff (φ : CoeffPair 2) :
    IsSelfAdjoint (sourceUnboundedOperator (by simp) φ) ↔ IsRealType (CoeffPair.toMax 2 φ) := by
  refine ⟨fun h => ?_,sourceUnboundedOperator_isSelfAdjoint φ⟩
  apply isRealType_of_sourceOperator_inner_symmetric φ
  have hs : (sourceUnboundedOperator (by simp) φ).IsFormalAdjoint
      (sourceUnboundedOperator (by simp) φ) := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp h] using
      LinearPMap.adjoint_isFormalAdjoint h.dense_domain
  intro a b
  simpa only [sourceUnboundedOperator_apply,sourceUnboundedDomainEquiv_coe] using
    hs (sourceUnboundedDomainEquiv a) (sourceUnboundedDomainEquiv b)

/-- The same characterization holds for the actual physical differential realization. -/
theorem physicalPeriodicOperator_isSelfAdjoint_iff (φ : CoeffPair 2) :
    IsSelfAdjoint (physicalPeriodicOperator φ) ↔ IsRealType (CoeffPair.toMax 2 φ) := by
  refine ⟨fun h => ?_,physicalPeriodicOperator_isSelfAdjoint φ⟩
  apply isRealType_of_sourceOperator_inner_symmetric φ
  have hs : (physicalPeriodicOperator φ).IsFormalAdjoint (physicalPeriodicOperator φ) := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp h] using
      LinearPMap.adjoint_isFormalAdjoint h.dense_domain
  intro a b
  simpa only [physicalPeriodicOperator_apply,physicalPeriodicDomainEquiv_coe,
    sourceCircleSynthesis.inner_map_map] using
    hs (physicalPeriodicDomainEquiv a) (physicalPeriodicDomainEquiv b)

/-- Period-one embedding preserves and reflects the original real-type condition. -/
theorem isRealType_periodOnePotential_iff (φ : CoeffPair 2) :
    IsRealType (periodOnePotential φ) ↔ IsRealType (CoeffPair.toMax 2 φ) := by
  refine ⟨fun h n => ?_,isRealType_periodOnePotential φ⟩
  change φ.snd n = conj (φ.fst (-n))
  have hh := h (2*n)
  change Coeff.periodDouble φ.snd (2*n) = conj (Coeff.periodDouble φ.fst (-(2*n))) at hh
  simpa only [show -(2*n) = 2*(-n) by ring,Coeff.periodDouble_even] using hh

/-- The original period-one physical operator is self-adjoint exactly for real-type potentials. -/
theorem sourcePhysicalPeriodicOperator_isSelfAdjoint_iff (φ : CoeffPair 2) :
    IsSelfAdjoint (physicalPeriodicOperator (periodOnePair φ)) ↔
      IsRealType (CoeffPair.toMax 2 φ) := by
  rw [physicalPeriodicOperator_isSelfAdjoint_iff]
  exact isRealType_periodOnePotential_iff φ

end NLS.ZakharovShabat
