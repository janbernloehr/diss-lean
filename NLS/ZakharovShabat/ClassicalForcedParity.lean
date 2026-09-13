import NLS.ZakharovShabat.PhysicalForcedEquation

/-!
# Exact boundary criteria for extending original parity root chains

For an original parity-domain source `b`, solving `(z-L)a=b` is equivalent
to the endpoint multiplier condition for the constructed forced solution.
With an initial vector specified, the original preimage is unique.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Signed endpoint matching lifts any physical C¹ vector to the original parity domain. -/
theorem exists_parity_domain_of_contDiff (r : ℤ) (u : ℝ → ℂ × ℂ) (hu : ContDiff ℝ 1 u)
    (hend : u 1 = wave r 1 • u 0) :
    ∃ a : Domain 2, a ∈ domainParitySubspace r ∧ EqOn (physicalDomain a) u (Icc 0 1) := by
  obtain ⟨a₁,ha₁,hs₁⟩ := exists_parity_sobolev_extension r hu.fst (congrArg Prod.fst hend)
  obtain ⟨a₂,ha₂,hs₂⟩ := exists_parity_sobolev_extension r hu.snd (congrArg Prod.snd hend)
  refine ⟨(a₁,a₂),fun n hn => ⟨ha₁ n hn,ha₂ n hn⟩,?_⟩
  intro x hx
  have hx2 : x ∈ Icc (0 : ℝ) 2 := ⟨hx.1,hx.2.trans (by norm_num)⟩
  apply Prod.ext
  · change sobolevSynthesis (by simp) a₁ (x : AddCircle (2 : ℝ)) = _
    rw [hs₁ x hx2,signedDouble_left _ _ hx.2]
  · change sobolevSynthesis (by simp) a₂ (x : AddCircle (2 : ℝ)) = _
    rw [hs₂ x hx2,signedDouble_left _ _ hx.2]

/-- Equal physical values on the unit interval determine the original parity-domain vector. -/
theorem physicalDomain_unit_injective_parity (r : ℤ) (a b : Domain 2)
    (ha : a ∈ domainParitySubspace r) (hb : b ∈ domainParitySubspace r)
    (he : EqOn (physicalDomain a) (physicalDomain b) (Icc 0 1)) : a = b := by
  apply sub_eq_zero.mp
  apply (physicalDomain_eq_zero_on_unit_iff (a-b) r ((domainParitySubspace r).sub_mem ha hb)).mp
  intro x hx
  have hs : physicalDomain (a-b) x = physicalDomain a x-physicalDomain b x := by
    apply Prod.ext
    · change sobolevSynthesis (by simp) (a.1-b.1) (x : AddCircle (2 : ℝ)) = _
      rw [map_sub,ContinuousMap.sub_apply]
      rfl
    · change sobolevSynthesis (by simp) (a.2-b.2) (x : AddCircle (2 : ℝ)) = _
      rw [map_sub,ContinuousMap.sub_apply]
      rfl
  rw [hs,he hx,sub_self]
  rfl

/-- Agreement with a forced solution transfers the original physical source equation. -/
theorem physical_unit_forcedEquation_of_eq (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (a b : Domain 2) (v : ℂ × ℂ)
    (ha : EqOn (physicalDomain a) (classicalForcedSolution Φ z (physicalDomainCurve b) v) (Icc 0 1)) :
    (fun x => z • physicalDomain a x-physicalOperator (physicalBase φ) (physicalDomain a) x)
      =ᵐ[volume.restrict (Ioc 0 1)] physicalDomain b := by
  simp only [Filter.EventuallyEq,ae_restrict_iff' measurableSet_Ioc] at hΦ ⊢
  filter_upwards [hΦ,(show ∀ᵐ x : ℝ, x ≠ (1 : ℝ) from by simp [ae_iff,measure_singleton])]
    with x hxΦ hx1
  intro hx
  have hxi : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1,lt_of_le_of_ne hx.2 hx1⟩
  have he : physicalDomain a =ᶠ[nhds x] classicalForcedSolution Φ z (physicalDomainCurve b) v := by
    filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with t ht
    exact ha ⟨ht.1.le,ht.2.le⟩
  have h₁ := (he.fun_comp Prod.fst).deriv_eq
  have h₂ := (he.fun_comp Prod.snd).deriv_eq
  simp only [Function.comp_def] at h₁ h₂
  have hc := physicalPencil_classicalForcedSolution Φ z (physicalDomainCurve b) v ⟨x,⟨hx.1.le,hx.2⟩⟩
  simp only [physicalOperator] at hc ⊢
  rw [h₁,h₂,hxΦ hx,ha ⟨hx.1.le,hx.2⟩]
  exact hc

/-- A fixed initial vector extends an original source precisely when its forced solution has the parity multiplier. -/
theorem exists_parity_preimage_iff_forced_endpoint (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (b : Domain 2) (hb : b ∈ domainParitySubspace r) (v : ℂ × ℂ) :
    (∃ a : Domain 2, a ∈ domainParitySubspace r ∧
      spectralPencil (by simp) φ z a = domainInclusion b ∧ physicalDomain a 0 = v) ↔
      classicalForcedSolution Φ z (physicalDomainCurve b) v 1 = wave r 1 • v := by
  constructor
  · rintro ⟨a,ha,he,hv⟩
    have hs := physicalDomain_eq_classicalForcedSolution φ Φ hΦ z a b he
    have ht := physicalDomain_add_one_of_parity a r ha 0
    rw [zero_add,hs (show (1 : ℝ) ∈ Icc 0 1 by simp),hv] at ht
    exact ht
  · intro hend
    obtain ⟨a,ha,hs⟩ := exists_parity_domain_of_contDiff r
      (classicalForcedSolution Φ z (physicalDomainCurve b) v)
      (contDiff_classicalForcedSolution Φ z (physicalDomainCurve b) v) (by simpa using hend)
    refine ⟨a,ha,?_,?_⟩
    · apply (spectralPencil_eq_inclusion_iff_physical_unit_parity φ hφ r z a b ha hb).mpr
      exact physical_unit_forcedEquation_of_eq φ Φ hΦ z a b v hs
    · simpa only [classicalForcedSolution_zero] using hs (show (0 : ℝ) ∈ Icc 0 1 by simp)

/-- The original parity preimage is unique once its initial vector is specified. -/
theorem parity_preimage_unique_of_initial (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (a c b : Domain 2)
    (ha : a ∈ domainParitySubspace r) (hc : c ∈ domainParitySubspace r)
    (hea : spectralPencil (by simp) φ z a = domainInclusion b)
    (hec : spectralPencil (by simp) φ z c = domainInclusion b)
    (h0 : physicalDomain a 0 = physicalDomain c 0) : a = c := by
  apply physicalDomain_unit_injective_parity r a c ha hc
  have hsa := physicalDomain_eq_classicalForcedSolution φ Φ hΦ z a b hea
  have hsc := physicalDomain_eq_classicalForcedSolution φ Φ hΦ z c b hec
  intro t ht
  rw [hsa ht,hsc ht,h0]

/-- Solvability of each original parity chain step reduces to a two-coordinate endpoint equation. -/
theorem exists_parity_preimage_iff_classical_boundary (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (b : Domain 2) (hb : b ∈ domainParitySubspace r) :
    (∃ a : Domain 2, a ∈ domainParitySubspace r ∧ spectralPencil (by simp) φ z a = domainInclusion b) ↔
      ∃ v : ℂ × ℂ, classicalSolution Φ z v 1-wave r 1 • v =
        -classicalForcedSolution Φ z (physicalDomainCurve b) 0 1 := by
  constructor
  · rintro ⟨a,ha,he⟩
    refine ⟨physicalDomain a 0,?_⟩
    apply (classicalForcedSolution_endpoint_iff Φ z (physicalDomainCurve b) _ (wave r 1)).mp
    exact (exists_parity_preimage_iff_forced_endpoint φ hφ Φ hΦ z r b hb _).mp ⟨a,ha,he,rfl⟩
  · rintro ⟨v,hv⟩
    have he := (classicalForcedSolution_endpoint_iff Φ z (physicalDomainCurve b) v (wave r 1)).mpr hv
    obtain ⟨a,ha,hea,_⟩ := (exists_parity_preimage_iff_forced_endpoint φ hφ Φ hΦ z r b hb v).mpr he
    exact ⟨a,ha,hea⟩

/-- The boundary criterion extends a prescribed original finite root chain by one step. -/
theorem exists_parity_root_extension_iff_classical_boundary (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) (r : ℤ) (b : Domain 2) (hb : b ∈ domainParitySubspace r) (k : ℕ)
    (hroot : domainInclusion b ∈ periodicRootSpace (by simp) φ z k) :
    (∃ a : Domain 2, a ∈ domainParitySubspace r ∧
      domainInclusion a ∈ periodicRootSpace (by simp) φ z (k+1) ∧
      spectralPencil (by simp) φ z a = domainInclusion b) ↔
      ∃ v : ℂ × ℂ, classicalSolution Φ z v 1-wave r 1 • v =
        -classicalForcedSolution Φ z (physicalDomainCurve b) 0 1 := by
  rw [← exists_parity_preimage_iff_classical_boundary φ hφ Φ hΦ z r b hb]
  constructor
  · rintro ⟨a,ha,_,he⟩
    exact ⟨a,ha,he⟩
  · rintro ⟨a,ha,he⟩
    exact ⟨a,ha,(mem_periodicRootSpace_succ (by simp) φ z k _).mpr ⟨a,rfl,he ▸ hroot⟩,he⟩

end NLS.ZakharovShabat
