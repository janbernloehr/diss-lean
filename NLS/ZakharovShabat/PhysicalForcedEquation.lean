import NLS.ZakharovShabat.ClassicalForcedSolution
import NLS.ZakharovShabat.ClassicalParityEigenvectors

/-!
# Original inhomogeneous pencil equations and physical initial values

The actual pencil `z-L` is realized on the physical interval with its source.
For even potentials and a fixed parity, equality of the original coefficient
vectors can be checked on the unit interval. Domain-valued sources then give
classical forced solutions, including for generalized eigenvector chains.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Restrict the original continuous domain representative to the unit interval. -/
def physicalDomainCurve (a : Domain 2) : Curve (ℂ × ℂ) :=
  ⟨fun t => physicalDomain a t,(continuous_physicalDomain a).comp continuous_subtype_val⟩

/-- The original spectral pencil has its actual inhomogeneous physical realization. -/
theorem physicalPencil_realization (φ : PairSpace 2) (z : ℂ) (a : Domain 2) :
    physicalBase (spectralPencil (by simp) φ z a) =ᵐ[volume.restrict (Ioc 0 2)]
      (fun x => z • physicalDomain a x-physicalOperator (physicalBase φ) (physicalDomain a) x) := by
  rw [spectralPencil_apply]
  filter_upwards [physicalBase_sub (z • domainInclusion a) (operator (by simp) φ a),
    physicalBase_smul z (domainInclusion a),physicalBase_domainInclusion a,
    physical_operator_realization φ a] with x hs hm hi ho
  rw [hs,hm,hi,ho]

/-- Any original domain-valued source equation gives the same equation on the unit interval. -/
theorem spectralPencil_eq_inclusion_physical_unit (φ : PairSpace 2) (z : ℂ) (a b : Domain 2)
    (he : spectralPencil (by simp) φ z a = domainInclusion b) :
    (fun x => z • physicalDomain a x-physicalOperator (physicalBase φ) (physicalDomain a) x)
      =ᵐ[volume.restrict (Ioc 0 1)] physicalDomain b := by
  have h := physicalPencil_realization φ z a
  rw [he] at h
  exact ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num)) (h.symm.trans (physicalBase_domainInclusion b))

/-- With fixed parity, checking the source equation on one unit interval is sufficient. -/
theorem spectralPencil_eq_inclusion_iff_physical_unit_parity (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (z : ℂ) (a b : Domain 2)
    (ha : a ∈ domainParitySubspace r) (hb : b ∈ domainParitySubspace r) :
    spectralPencil (by simp) φ z a = domainInclusion b ↔
      (fun x => z • physicalDomain a x-physicalOperator (physicalBase φ) (physicalDomain a) x)
        =ᵐ[volume.restrict (Ioc 0 1)] physicalDomain b := by
  refine ⟨spectralPencil_eq_inclusion_physical_unit φ z a b,?_⟩
  intro he
  apply sub_eq_zero.mp
  apply pairParity_eq_zero_of_physicalBase_unit _ r
  · rw [spectralPencil_apply]
    exact (pairParitySubspace r).sub_mem
      ((pairParitySubspace r).sub_mem
        ((pairParitySubspace r).smul_mem z ((mem_domainParitySubspace r a).mp ha))
        (operator_mem_pairParitySubspace (by simp) φ hφ r a ha))
      ((mem_domainParitySubspace r b).mp hb)
  · have hs := physicalBase_sub (spectralPencil (by simp) φ z a) (domainInclusion b)
    have hp := physicalPencil_realization φ z a
    have hb' := physicalBase_domainInclusion b
    have hfull : physicalBase (spectralPencil (by simp) φ z a-domainInclusion b)
        =ᵐ[volume.restrict (Ioc 0 2)] (fun x =>
          (z • physicalDomain a x-physicalOperator (physicalBase φ) (physicalDomain a) x)-physicalDomain b x) := by
      filter_upwards [hs,hp,hb'] with x hsx hpx hbx
      rw [hsx,hpx,hbx]
    have hunit := ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num)) hfull
    filter_upwards [hunit,he] with x hx hex
    simp only [hx,hex,sub_self,Pi.zero_apply]

/-- An original domain source gives the expected inhomogeneous derivative almost everywhere. -/
theorem ae_hasDerivAt_physicalDomain_forced (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (a b : Domain 2) (he : spectralPencil (by simp) φ z a = domainInclusion b) :
    ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 → HasDerivAt (physicalDomain a)
      (extend (classicalCoefficientCurveCLM (z,Φ)) s (physicalDomain a s)+
        extend (classicalSourceCurve (physicalDomainCurve b)) s) s := by
  have hO := spectralPencil_eq_inclusion_physical_unit φ z a b he
  simp only [Filter.EventuallyEq,ae_restrict_iff' measurableSet_Ioc] at hO hΦ
  filter_upwards [hO,hΦ,
    NLS.FunctionalAnalysis.ae_differentiableAt_complex (absolutelyContinuous_sobolevSynthesis a.1),
    NLS.FunctionalAnalysis.ae_differentiableAt_complex (absolutelyContinuous_sobolevSynthesis a.2),
    (show ∀ᵐ s : ℝ, s ≠ (0 : ℝ) from by simp [ae_iff,measure_singleton])]
      with s hsO hsΦ hs₁ hs₂ hs0
  intro hs
  have hs' : s ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0),hs.2⟩
  have hs2 : s ∈ uIcc (0 : ℝ) 2 := by
    rw [uIcc_of_le (by norm_num)]
    exact ⟨hs.1,hs.2.trans (by norm_num)⟩
  have hD := hasDerivAt_of_physicalPencil_eq (hs₁ hs2) (hs₂ hs2) (hsO hs')
  rw [hsΦ hs'] at hD
  simpa only [LinearVolterra.extend,projIcc_of_mem _ hs,classicalCoefficientCurveCLM_apply,
    classicalSourceCurve,physicalDomainCurve,ContinuousMap.coe_mk] using hD

/-- Every original domain-valued source equation agrees with the actual classical forced solution. -/
theorem physicalDomain_eq_classicalForcedSolution (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (a b : Domain 2) (he : spectralPencil (by simp) φ z a = domainInclusion b) :
    EqOn (physicalDomain a)
      (classicalForcedSolution Φ z (physicalDomainCurve b) (physicalDomain a 0)) (Icc 0 1) := by
  apply forcedSolution_unique_of_ac
  · exact (absolutelyContinuous_physicalDomain a).mono (by
      simp only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num),
        uIcc_of_le (show (0 : ℝ) ≤ 2 by norm_num)]
      exact Icc_subset_Icc le_rfl (by norm_num))
  · exact ae_hasDerivAt_physicalDomain_forced φ Φ hΦ z a b he

end NLS.ZakharovShabat
