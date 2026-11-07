import NLS.KdV.SingularHillSpectrum

/-! Full physical algebraic root spaces for ALL original complex H-minus-one
potentials. Every repeated application retains the original H1 domain. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.FunctionalAnalysis

/-- The actual full original physical pencil at a resolvent point, as a Banach isomorphism. -/
def singularHillPencilEquiv (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) :
    FourierLebesgueSpace (2:ℝ) 1 2 ≃L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  ContinuousLinearEquiv.ofBijective
    (singularHillOperator q -
      a • singularHillDomainInclusion)
        (LinearMap.ker_eq_bot.mpr ha.1) (LinearMap.range_eq_top.mpr ha.2)

theorem singularHillPencilEquiv_apply (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillPencilEquiv q a ha f =
      singularHillOperator q f -
        a • singularHillDomainInclusion f := rfl

/-- The inverse is the already constructed actual original-domain resolvent. -/
theorem singularHillPencilEquiv_symm (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) (g : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    (singularHillPencilEquiv q a ha).symm g = singularHillResolventToH1 q a g := by
  apply (singularHillPencilEquiv q a ha).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, singularHillPencilEquiv_apply]
  exact (singularHillResolventToH1_right q a ha g).symm

/-- The generic base resolvent is the exact original compact H-minus-one resolvent. -/
theorem pencilResolvent_singularHillPencilEquiv (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularHillResolventSet q) :
    pencilResolvent singularHillDomainInclusion.toLinearMap
      (singularHillPencilEquiv q a ha).toLinearEquiv =
        (singularHillBaseResolvent q a).toLinearMap := by
  ext g
  change singularHillDomainInclusion ((singularHillPencilEquiv q a ha).symm g) = _
  rw [singularHillPencilEquiv_symm]
  rfl

/-- The original physical pencil is exactly the spectral shift of this domain-to-base isomorphism. -/
theorem singularHillPencil_eq_resolvent_shift (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularHillResolventSet q) :
    (singularHillOperator q -
      z • singularHillDomainInclusion).toLinearMap =
      (singularHillPencilEquiv q a ha).toLinearMap -
        (z-a) • singularHillDomainInclusion.toLinearMap := by
  ext f
  change singularHillOperator q f -
    z • singularHillDomainInclusion f =
      singularHillPencilEquiv q a ha f - (z-a) • singularHillDomainInclusion f
  rw [singularHillPencilEquiv_apply, sub_smul]
  abel

/-- Every actual finite physical root-chain level equals the corresponding compact-resolvent generalized eigenspace. -/
theorem singularHillRootSpace_eq_resolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularHillResolventSet q) (hza : z ≠ a) (n : ℕ) :
    singularHillRootSpace q z n =
      Module.End.genEigenspace (singularHillBaseResolvent q a).toLinearMap (z-a)⁻¹ n := by
  unfold singularHillRootSpace
  rw [singularHillPencil_eq_resolvent_shift q a z ha]
  have h := pencilRootSpace_eq_resolvent_genEigenspace singularHillDomainInclusion.toLinearMap
    singularHillDomainInclusion_injective (singularHillPencilEquiv q a ha).toLinearEquiv
      (z-a) (sub_ne_zero.mpr hza) n
  rwa [pencilResolvent_singularHillPencilEquiv] at h

/-- The full physical algebraic root space equals the complete nonzero compact-resolvent generalized eigenspace. -/
theorem singularHillRootSpaceTop_eq_resolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularHillResolventSet q) (hza : z ≠ a) :
    singularHillRootSpaceTop q z =
      Module.End.genEigenspace (singularHillBaseResolvent q a).toLinearMap (z-a)⁻¹ ⊤ := by
  unfold singularHillRootSpaceTop
  rw [singularHillPencil_eq_resolvent_shift q a z ha]
  have h := pencilRootSpaceTop_eq_resolvent_genEigenspace singularHillDomainInclusion.toLinearMap
    singularHillDomainInclusion_injective (singularHillPencilEquiv q a ha).toLinearEquiv
      (z-a) (sub_ne_zero.mpr hza)
  rwa [pencilResolvent_singularHillPencilEquiv] at h

/-- A physical resolvent point has no nonzero actual algebraic root vectors. -/
theorem singularHillRootSpaceTop_eq_bot_of_mem_resolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (hz : z ∈ singularHillResolventSet q) :
    singularHillRootSpaceTop q z = ⊥ :=
  pencilRootSpaceTop_eq_bot_of_injective singularHillDomainInclusion.toLinearMap
    (singularHillOperator q -
      z • singularHillDomainInclusion).toLinearMap hz.1

/-- Full physical algebraic root spaces are finite dimensional at every complex parameter. -/
theorem finiteDimensional_singularHillRootSpaceTop (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    FiniteDimensional ℂ (singularHillRootSpaceTop
      q z) := by
  obtain ⟨a,ha⟩ := singularHillResolventSet_nonempty q
  by_cases hza : z = a
  · subst z
    rw [singularHillRootSpaceTop_eq_bot_of_mem_resolvent q a ha]
    infer_instance
  · rw [singularHillRootSpaceTop_eq_resolvent q a z ha hza]
    exact CompactSpectrum.finiteDimensional_genEigenspace_top
      (singularHillBaseResolvent q a) (isCompactOperator_singularHillBaseResolvent q a)
        (inv_ne_zero (sub_ne_zero.mpr hza))

/-- The full physical algebraic root space is attained at a finite chain length. -/
theorem exists_singularHillRootSpace_eq_top (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    ∃ N : ℕ, singularHillRootSpace q z N =
      singularHillRootSpaceTop q z := by
  obtain ⟨a,ha⟩ := singularHillResolventSet_nonempty q
  by_cases hza : z = a
  · subst z
    refine ⟨0,?_⟩
    rw [singularHillRootSpaceTop_eq_bot_of_mem_resolvent q a ha]
    rfl
  · obtain ⟨N,hN⟩ := CompactSpectrum.exists_genEigenspace_eq_top
      (singularHillBaseResolvent q a) (isCompactOperator_singularHillBaseResolvent q a)
        (inv_ne_zero (sub_ne_zero.mpr hza))
    exact ⟨N,by rw [singularHillRootSpace_eq_resolvent q a z ha hza,
      singularHillRootSpaceTop_eq_resolvent q a z ha hza]; exact hN⟩

/-- The actual finite physical algebraic multiplicity, defined from the full original root space. -/
def singularHillAlgebraicMultiplicity (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) : ℕ :=
  letI := finiteDimensional_singularHillRootSpaceTop q z
  Module.finrank ℂ (singularHillRootSpaceTop q z)

/-- Actual algebraic multiplicity equals that of any actual compact resolvent at the transformed value. -/
theorem singularHillAlgebraicMultiplicity_eq_resolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularHillResolventSet q) (hza : z ≠ a) :
    singularHillAlgebraicMultiplicity q z = Module.finrank ℂ
      (Module.End.genEigenspace (singularHillBaseResolvent q a).toLinearMap (z-a)⁻¹ ⊤) := by
  unfold singularHillAlgebraicMultiplicity
  rw [singularHillRootSpaceTop_eq_resolvent q a z ha hza]

/-- The eventual finite root-chain levels all equal the full physical algebraic root space. -/
theorem singularHillRootSpace_stabilizes (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      singularHillRootSpace q z n =
        singularHillRootSpaceTop q z := by
  obtain ⟨N,hN⟩ := exists_singularHillRootSpace_eq_top q z
  refine ⟨N,fun n hn => le_antisymm ?_ ?_⟩
  · exact le_iSup (fun n => singularHillRootSpace
      q z n) n
  · rw [← hN]
    exact pencilRootSpace_mono _ _ hn

/-- Actual physical algebraic multiplicity is positive exactly on the actual physical spectrum. -/
theorem singularHillAlgebraicMultiplicity_pos_iff (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    0 < singularHillAlgebraicMultiplicity q z ↔ z ∈ singularHillSpectrum q := by
  let := finiteDimensional_singularHillRootSpaceTop q z
  constructor
  · intro h
    by_contra hnot
    have hz : z ∈ singularHillResolventSet q := by
      simpa only [singularHillSpectrum, Set.mem_compl_iff, not_not] using hnot
    unfold singularHillAlgebraicMultiplicity at h
    rw [singularHillRootSpaceTop_eq_bot_of_mem_resolvent q z hz, finrank_bot] at h
    exact Nat.not_lt_zero _ h
  · intro hz
    obtain ⟨f,hf0,hf⟩ := (mem_singularHillSpectrum_iff q z).mp hz
    have hlevel : singularHillDomainInclusion f ∈
        singularHillRootSpace q z 1 :=
      (mem_singularHillRootSpace_one _ z _).mpr ⟨f,rfl,hf⟩
    have htop : singularHillDomainInclusion f ∈
        singularHillRootSpaceTop q z :=
      (mem_singularHillRootSpaceTop _ z _).mpr ⟨1,hlevel⟩
    change 0 < Module.finrank ℂ (singularHillRootSpaceTop
      q z)
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨singularHillDomainInclusion f,htop⟩,?_⟩
    intro he
    apply hf0
    apply singularHillDomainInclusion_injective
    have h := congrArg Subtype.val he
    change singularHillDomainInclusion f = (0 : FourierLebesgueSpace (2:ℝ) (-1) 2) at h
    simpa only [map_zero] using h


/-- The actual physical algebraic multiplicity is unchanged at endpoint realizations. -/
theorem singularHillAlgebraicMultiplicity_endpoint (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (z : ℂ) :
    singularHillAlgebraicMultiplicity (endpointHillHminusOne SpectralWeight.one r hr1 q) z =
      endpointHillAlgebraicMultiplicity r hr hr1 q z := rfl

/-- At a nonreal value, every real original H-minus-one potential has zero
ACTUAL physical algebraic multiplicity. -/
theorem singularHillAlgebraicMultiplicity_eq_zero_of_im_ne_zero
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (hq : q.val = q.val.conjugate)
    (z : ℂ) (hz : z.im ≠ 0) : singularHillAlgebraicMultiplicity q z = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro hp
  exact hz (singularHillSpectrum_im_zero_of_real q hq z
    ((singularHillAlgebraicMultiplicity_pos_iff q z).mp hp))

end NLS.KdV
