import NLS.ZakharovShabat.UnitParityOperatorDomain
import NLS.ZakharovShabat.ParitySelfAdjointRealType
import NLS.ZakharovShabat.SourcePhysicalRealL2
import NLS.ZakharovShabat.ClassicalIntervalOperator

/-! # The actual periodic and antiperiodic operators on unit-interval L² -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The even sign is precisely the classical periodic endpoint condition. -/
theorem hasClassicalParityDomain_zero_iff (f : ℝ → ℂ × ℂ) :
    HasClassicalParityDomain 0 f ↔
      Fourier.HasIntervalH1Regularity (fun x => (f x).1) ∧
      Fourier.HasIntervalH1Regularity (fun x => (f x).2) ∧ f 1 = f 0 := by
  constructor
  · intro h
    exact ⟨h.fst_regular,h.snd_regular,by simpa only [Fourier.wave_zero,one_smul] using h.boundary⟩
  · rintro ⟨h₁,h₂,hb⟩
    exact ⟨h₁,h₂,by simpa only [Fourier.wave_zero,one_smul] using hb⟩

/-- The odd sign is precisely the classical antiperiodic endpoint condition. -/
theorem hasClassicalParityDomain_one_iff (f : ℝ → ℂ × ℂ) :
    HasClassicalParityDomain 1 f ↔
      Fourier.HasIntervalH1Regularity (fun x => (f x).1) ∧
      Fourier.HasIntervalH1Regularity (fun x => (f x).2) ∧ f 1 = -f 0 := by
  have hw : Fourier.wave 1 1 = -1 := by simpa using Fourier.wave_odd_at_one 0
  constructor
  · intro h
    exact ⟨h.fst_regular,h.snd_regular,by simpa only [hw,neg_one_smul] using h.boundary⟩
  · rintro ⟨h₁,h₂,hb⟩
    exact ⟨h₁,h₂,by simpa only [hw,neg_one_smul] using hb⟩

/-- The signed physical expression on exactly one included parity domain. -/
def unitParityOperator (φ : CoeffPair 2) (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) :
    IntervalPairL2 →ₗ.[ℂ] IntervalPairL2 where
  domain := LinearMap.range (unitParityDomainInclusion r).toLinearMap
  toFun := (sourceParityUnitEquiv r).toLinearEquiv.toLinearMap.comp
    ((sourceParityOperator (by simp) φ hφ r).toLinearMap.comp
      (unitParityDomainEquiv r).symm.toLinearMap)

@[simp] theorem unitParityOperator_apply (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (a : sourceDomainParitySubspace (p := 2) r) :
    unitParityOperator φ hφ r (unitParityDomainEquiv r a) =
      sourceParityUnitEquiv r (sourceParityOperator (by simp) φ hφ r a) := by
  change sourceParityUnitEquiv r (sourceParityOperator (by simp) φ hφ r
    ((unitParityDomainEquiv r).symm (unitParityDomainEquiv r a))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem unitParityOperator_formal_symmetric (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (hreal : IsRealType (CoeffPair.toMax 2 φ)) (r : ℤ) :
    (unitParityOperator φ hφ r).IsFormalAdjoint (unitParityOperator φ hφ r) := by
  intro x y
  obtain ⟨a,rfl⟩ := (unitParityDomainEquiv r).surjective x
  obtain ⟨b,rfl⟩ := (unitParityDomainEquiv r).surjective y
  simpa only [unitParityOperator_apply,unitParityDomainEquiv_coe,
    (sourceParityUnitEquiv r).inner_map_map,Submodule.coe_inner,
    sourceParityOperator_coe,sourceParityDomainInclusion_coe] using sourceOperator_inner_symmetric φ hreal a b

set_option backward.isDefEq.respectTransparency false in
theorem unitParityOperator_pencil_surjective (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ)
    (hz : z ∈ sourceResolventSet (by simp) φ) :
    Function.Surjective (linearPMapPencil (unitParityOperator φ hφ r) z) := by
  intro y
  let a := sourceParityResolventToDomain (by simp) φ hφ r z hz
    ((sourceParityUnitEquiv r).symm y)
  refine ⟨unitParityDomainEquiv r a,?_⟩
  rw [linearPMapPencil_apply,unitParityDomainEquiv_coe,unitParityOperator_apply,
    ← map_smul,← map_sub]
  have he : z • sourceParityDomainInclusion r a - sourceParityOperator (by simp) φ hφ r a =
      (sourceParityUnitEquiv r).symm y :=
    sourceParitySpectralPencil_resolvent (by simp) φ hφ r z hz _
  rw [he,LinearIsometryEquiv.apply_symm_apply]

/-- Equality with the actual Hilbert adjoint on the original unit-interval L² space, including domains. -/
theorem unitParityOperator_isSelfAdjoint (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (hreal : IsRealType (CoeffPair.toMax 2 φ)) (r : ℤ) :
    IsSelfAdjoint (unitParityOperator φ hφ r) := by
  apply isSelfAdjoint_of_conjugate_pencils_surjective (unitParityOperator φ hφ r)
    (unitParityDomainInclusion_denseRange r)
    (unitParityOperator_formal_symmetric φ hφ hreal r) Complex.I
  · apply unitParityOperator_pencil_surjective
    rw [sourceResolventSet_eq]
    exact mem_resolventSet_of_realType_of_im_ne_zero (by simp) _ hreal _ (by simp)
  · apply unitParityOperator_pencil_surjective
    rw [sourceResolventSet_eq]
    exact mem_resolventSet_of_realType_of_im_ne_zero (by simp) _ hreal _ (by simp)

/-- Restriction retains the original differential expression for arbitrary even L² potentials. -/
theorem unitParityOperator_representative (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (a : sourceDomainParitySubspace (p := 2) r) :
    intervalL2Representative (unitParityOperator φ hφ r (unitParityDomainEquiv r a) : IntervalPairL2)
      =ᵐ[volume.restrict (Ioc 0 1)]
      physicalOperator (physicalBase (CoeffPair.toMax 2 φ))
        (physicalDomain (WeightedCoeffPair.toMax (Weight.sobolev 1) 2 a.val)) := by
  rw [unitParityOperator_apply]
  apply (sourceParityUnitEquiv_representative r (sourceParityOperator (by simp) φ hφ r a)).trans
  exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (physical_operator_realization _ _)

/-- An original period-one real potential gives both separate physical self-adjoint operators. -/
theorem sourceUnitParityOperator_isSelfAdjoint (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (r : ℤ) :
    IsSelfAdjoint (unitParityOperator (periodOnePair φ) (periodOnePotential_mem φ) r) :=
  unitParityOperator_isSelfAdjoint _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ) r

/-- The exact partial-operator domain is the full classical signed H¹ domain. -/
theorem unitParityOperator_domain_iff (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (u : IntervalPairL2) :
    u ∈ (unitParityOperator φ hφ r).domain ↔
      ∃ (f : ℝ → ℂ × ℂ) (hf : HasClassicalParityDomain r f), intervalL2OfFunction f hf.memLp = u :=
  mem_unitParityDomain_iff r u

/-- Either actual classical unit-interval realization is self-adjoint exactly for real type. -/
theorem unitParityOperator_isSelfAdjoint_iff (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) :
    IsSelfAdjoint (unitParityOperator φ hφ r) ↔ IsRealType (CoeffPair.toMax 2 φ) := by
  refine ⟨fun h => ?_,fun h => unitParityOperator_isSelfAdjoint φ hφ h r⟩
  apply isRealType_of_sourceParityOperator_inner_symmetric φ hφ r
  have hs : (unitParityOperator φ hφ r).IsFormalAdjoint (unitParityOperator φ hφ r) := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp h] using
      LinearPMap.adjoint_isFormalAdjoint h.dense_domain
  intro a b
  simpa only [unitParityOperator_apply,unitParityDomainEquiv_coe,
    (sourceParityUnitEquiv r).inner_map_map] using
    hs (unitParityDomainEquiv r a) (unitParityDomainEquiv r b)

/-- The original period-one source potential has the precise classical signed adjoint characterization. -/
theorem sourceUnitParityOperator_isSelfAdjoint_iff (φ : CoeffPair 2) (r : ℤ) :
    IsSelfAdjoint (unitParityOperator (periodOnePair φ) (periodOnePotential_mem φ) r) ↔
      IsRealType (CoeffPair.toMax 2 φ) :=
  (unitParityOperator_isSelfAdjoint_iff (periodOnePair φ) (periodOnePotential_mem φ) r).trans
    (isRealType_periodOnePotential_iff φ)

/-- The included classical function is acted on by its own actual derivative and original potential. -/
theorem unitParityOperator_classical_representative (φ : CoeffPair 2)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalParityDomain r f) :
    intervalL2Representative (unitParityOperator φ hφ r
      (unitParityDomainEquiv r (sourceClassicalParityExtension r f hf)))
      =ᵐ[volume.restrict (Ioc 0 1)] physicalOperator (physicalBase (CoeffPair.toMax 2 φ)) f := by
  apply (unitParityOperator_representative φ hφ r (sourceClassicalParityExtension r f hf)).trans
  apply physicalOperator_congr_on_interval Filter.EventuallyEq.rfl
  intro x hx
  change physicalDomain ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2)
    ((WeightedCoeffPair.toMax (Weight.sobolev 1) 2).symm (classicalParityExtension r f hf))) x = f x
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact classicalParityExtension_restrict r f hf hx

/-- The signed classical operator parameterized by an arbitrary actual unit-interval L² potential. -/
def classicalSignedOperator (u : IntervalPairL2) (r : ℤ) : IntervalPairL2 →ₗ.[ℂ] IntervalPairL2 :=
  unitParityOperator (periodOnePair (sourcePhysicalL2Equiv.symm u))
    (periodOnePotential_mem (sourcePhysicalL2Equiv.symm u)) r

/-- Exact adjoint equality for the physical periodic or antiperiodic operator characterizes real type. -/
theorem classicalSignedOperator_isSelfAdjoint_iff (u : IntervalPairL2) (r : ℤ) :
    IsSelfAdjoint (classicalSignedOperator u r) ↔ IsClassicalRealType (intervalL2Representative u) := by
  apply (sourceUnitParityOperator_isSelfAdjoint_iff (sourcePhysicalL2Equiv.symm u) r).trans
  simpa only [sourcePhysicalL2_equiv_symm,mem_realTypeSourceSubmodule] using
    (sourcePhysicalL2_realType_iff (sourcePhysicalL2Equiv.symm u)).symm

/-- The original physical operator has exactly the classical signed H¹ domain, for every L² potential. -/
theorem classicalSignedOperator_domain_iff (u v : IntervalPairL2) (r : ℤ) :
    v ∈ (classicalSignedOperator u r).domain ↔
      ∃ (f : ℝ → ℂ × ℂ) (hf : HasClassicalParityDomain r f), intervalL2OfFunction f hf.memLp = v :=
  mem_unitParityDomain_iff r v

/-- Both the arbitrary physical L² potential and full classical H¹ input appear in the actual expression. -/
theorem classicalSignedOperator_representative (u : IntervalPairL2) (r : ℤ)
    (f : ℝ → ℂ × ℂ) (hf : HasClassicalParityDomain r f) :
    intervalL2Representative (classicalSignedOperator u r
      (unitParityDomainEquiv r (sourceClassicalParityExtension r f hf)))
      =ᵐ[volume.restrict (Ioc 0 1)] physicalOperator (intervalL2Representative u) f := by
  apply (unitParityOperator_classical_representative _ _ r f hf).trans
  have hp := sourcePhysicalL2_representative (sourcePhysicalL2Equiv.symm u)
  rw [sourcePhysicalL2_equiv_symm] at hp
  exact physicalOperator_congr_on_interval hp.symm (fun _ _ => rfl)

end NLS.ZakharovShabat
