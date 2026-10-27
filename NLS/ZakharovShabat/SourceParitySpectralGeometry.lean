import NLS.ZakharovShabat.SourceParityCompactResolvent
import NLS.ZakharovShabat.ParityRootMultiplicity

/-! # Discrete sector spectra and the original parity multiplicities -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A sector resolvent parameter is a unit of the compact-resolvent pencil at any fixed sector base point. -/
theorem mem_sourceParityResolventSet_iff_shift_isUnit (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (w z : ℂ)
    (hw : w ∈ sourceParityResolventSet hp φ hφ r) :
    z ∈ sourceParityResolventSet hp φ hφ r ↔
      IsUnit (1 + (z-w) • sourceParityFullResolvent hp φ hφ r w hw) := by
  let : CompleteSpace (sourceParitySubspace (p := p) r) :=
    (isClosed_sourceParitySubspace r).completeSpace_coe
  have hR : Function.Bijective (sourceParityFullResolventToDomain hp φ hφ r w hw) :=
    (sourceParityPencilEquiv hp φ hφ r w hw).symm.bijective
  rw [← sourceParityPencil_comp_fullResolvent,ContinuousLinearMap.isUnit_iff_bijective]
  exact (Function.Bijective.of_comp_iff _ hR).symm

theorem isOpen_sourceParityResolventSet (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) : IsOpen (sourceParityResolventSet hp φ hφ r) := by
  let : CompleteSpace (sourceParitySubspace (p := p) r) :=
    (isClosed_sourceParitySubspace r).completeSpace_coe
  obtain ⟨w,hw⟩ := resolventSet_nonempty hp (CoeffPair.toMax p φ)
  have hw' : w ∈ sourceResolventSet hp φ := by rwa [sourceResolventSet_eq]
  let hr := mem_sourceParityResolventSet_of_full hp φ hφ r w hw'
  have he : sourceParityResolventSet hp φ hφ r =
      (fun z : ℂ => 1 + (z-w) • sourceParityFullResolvent hp φ hφ r w hr) ⁻¹' {A | IsUnit A} := by
    ext z
    exact mem_sourceParityResolventSet_iff_shift_isUnit hp φ hφ r w z hr
  rw [he]
  apply (show IsOpen {A : sourceParitySubspace (p := p) r →L[ℂ] sourceParitySubspace (p := p) r | IsUnit A}
    from Units.isOpen (R := sourceParitySubspace (p := p) r →L[ℂ] sourceParitySubspace (p := p) r)).preimage
  exact continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)

theorem isClosed_sourceParitySpectrum (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) : IsClosed (sourceParitySpectrum hp φ hφ r) :=
  (isOpen_sourceParityResolventSet hp φ hφ r).isClosed_compl

theorem sourceParitySpectrum_subset_full (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) :
    sourceParitySpectrum hp φ hφ r ⊆ (sourceResolventSet hp φ)ᶜ :=
  fun z hz hw => hz (mem_sourceParityResolventSet_of_full hp φ hφ r z hw)

/-- Every bounded part of either actual sector spectrum is finite. -/
theorem finite_sourceParitySpectrum_inter_of_isBounded (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) {K : Set ℂ} (hK : Bornology.IsBounded K) :
    Set.Finite (sourceParitySpectrum hp φ hφ r ∩ K) := by
  have hs : sourceParitySpectrum hp φ hφ r ⊆ periodicSpectrum hp (CoeffPair.toMax p φ) := by
    simpa only [sourceResolventSet_eq,periodicSpectrum] using sourceParitySpectrum_subset_full hp φ hφ r
  exact (finite_periodicSpectrum_inter_of_isBounded hp _ hK).subset (Set.inter_subset_inter_left K hs)

theorem discreteTopology_sourceParitySpectrum (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) : DiscreteTopology (sourceParitySpectrum hp φ hφ r) := by
  apply continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact
  rw [tendsto_cofinite_cocompact_iff]
  intro K hK
  exact Set.Finite.of_injOn
    (fun z hz => show (z : ℂ) ∈ sourceParitySpectrum hp φ hφ r ∩ K from ⟨z.property,hz⟩)
    (fun _ _ _ _ h => Subtype.ext h) (finite_sourceParitySpectrum_inter_of_isBounded hp φ hφ r hK.isBounded)

/-- The independently defined sector spectrum is precisely positivity of the original algebraic multiplicity. -/
theorem mem_sourceParitySpectrum_iff_multiplicity_pos (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceParitySubspace 0) (r : ℤ) (z : ℂ) :
    z ∈ sourceParitySpectrum hp φ hφ r ↔ 0 < parityAlgebraicMultiplicity hp (CoeffPair.toMax p φ) r z := by
  rw [mem_sourceParitySpectrum_iff_exists_kernel,parityAlgebraicMultiplicity_pos_iff hp (CoeffPair.toMax p φ) hφ r z]
  constructor
  · rintro ⟨a,hne,ha⟩
    refine ⟨WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val,?_,a.property,?_⟩
    · intro h
      apply hne
      apply Subtype.ext
      exact (WeightedCoeffPair.toMax (Weight.sobolev 1) p).injective (h.trans (map_zero _).symm)
    · have he := congrArg Subtype.val ha
      rw [sourceParitySpectralPencil_coe] at he
      have hh := congrArg (CoeffPair.toMax p) he
      change (CoeffPair.toMax p) ((CoeffPair.toMax p).symm
        (spectralPencil hp (CoeffPair.toMax p φ) z (WeightedCoeffPair.toMax (Weight.sobolev 1) p a.val))) =
        (CoeffPair.toMax p) 0 at hh
      simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero] using hh
  · rintro ⟨f,hne,hf,hz⟩
    let a : sourceDomainParitySubspace (p := p) r :=
      ⟨(WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm f,by
        change (WeightedCoeffPair.toMax (Weight.sobolev 1) p)
          ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm f) ∈ domainParitySubspace r
        rwa [ContinuousLinearEquiv.apply_symm_apply]⟩
    refine ⟨a,?_,?_⟩
    · intro h
      apply hne
      have he := congrArg (fun b : sourceDomainParitySubspace (p := p) r =>
        WeightedCoeffPair.toMax (Weight.sobolev 1) p b.val) h
      change (WeightedCoeffPair.toMax (Weight.sobolev 1) p)
        ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm f) = (WeightedCoeffPair.toMax (Weight.sobolev 1) p) 0 at he
      simpa only [ContinuousLinearEquiv.apply_symm_apply,map_zero] using he
    · apply Subtype.ext
      rw [sourceParitySpectralPencil_coe]
      change (CoeffPair.toMax p).symm (spectralPencil hp (CoeffPair.toMax p φ) z
        ((WeightedCoeffPair.toMax (Weight.sobolev 1) p)
          ((WeightedCoeffPair.toMax (Weight.sobolev 1) p).symm f))) = 0
      rw [ContinuousLinearEquiv.apply_symm_apply,hz,map_zero]

/-- At every free lattice point, the actual spectrum selects precisely its Fourier parity. -/
theorem mem_sourceParitySpectrum_zero_lattice_iff (hp : p ≠ ⊤) (r n : ℤ) :
    (Real.pi : ℂ)*n ∈ sourceParitySpectrum hp (0 : CoeffPair p) (Submodule.zero_mem _) r ↔ n%2 = r%2 := by
  rw [mem_sourceParitySpectrum_iff_multiplicity_pos,map_zero,parityAlgebraicMultiplicity_zero]
  by_cases h : n%2 = r%2 <;> simp [h]

/-- The opposite sector can be invertible at an actual eigenvalue of the full period-two operator. -/
theorem zero_mem_odd_resolvent_and_even_spectrum (hp : p ≠ ⊤) :
    (0 : ℂ) ∈ sourceParityResolventSet hp (0 : CoeffPair p) (Submodule.zero_mem _) 1 ∧
      (0 : ℂ) ∈ sourceParitySpectrum hp (0 : CoeffPair p) (Submodule.zero_mem _) 0 := by
  have hodd := mem_sourceParitySpectrum_zero_lattice_iff (p := p) hp 1 0
  have heven := mem_sourceParitySpectrum_zero_lattice_iff (p := p) hp 0 0
  simpa [sourceParitySpectrum] using And.intro hodd heven

end NLS.ZakharovShabat
