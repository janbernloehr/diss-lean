import NLS.KdV.SingularDirichletSpectrum
import NLS.KdV.SingularDirichletRootSpace
import NLS.FunctionalAnalysis.ResolventRootSpace
import NLS.FunctionalAnalysis.CompactGeneralized

/-! Full native algebraic root spaces for ALL original complex H-minus-one
potentials. Every repeated application retains the entire zero-trace H1 domain
and full dual base. Compact resolvents prove finiteness and stabilization;
characteristic-order matching is a separate assertion. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.FunctionalAnalysis
local instance dirichletAlgebraicH1NormedGroup : NormedAddCommGroup UnitDirichletH1 :=
  unitDirichletSubspace.normedAddCommGroup
local instance dirichletAlgebraicH1NormedSpace : NormedSpace ℂ UnitDirichletH1 :=
  unitDirichletSubspace.normedSpace
local instance dirichletAlgebraicBaseNormedGroup : NormedAddCommGroup UnitDirichletHminus := inferInstance
local instance dirichletAlgebraicBaseNormedSpace : NormedSpace ℂ UnitDirichletHminus := inferInstance

/-- The actual full original physical pencil at a resolvent point, as a Banach isomorphism. -/
def singularDirichletPencilEquiv (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) :
    UnitDirichletH1 ≃L[ℂ] UnitDirichletHminus :=
  ContinuousLinearEquiv.ofBijective
    (singularDirichletOperator q -
      a • singularDirichletDomainInclusion)
        (LinearMap.ker_eq_bot.mpr ha.1) (LinearMap.range_eq_top.mpr ha.2)

theorem singularDirichletPencilEquiv_apply (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) (f : UnitDirichletH1) :
    singularDirichletPencilEquiv q a ha f =
      singularDirichletOperator q f -
        a • singularDirichletDomainInclusion f := rfl

/-- The inverse is the already constructed actual original-domain resolvent. -/
theorem singularDirichletPencilEquiv_symm (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) (g : UnitDirichletHminus) :
    (singularDirichletPencilEquiv q a ha).symm g = singularDirichletResolventToH1 q a g := by
  apply (singularDirichletPencilEquiv q a ha).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, singularDirichletPencilEquiv_apply]
  exact (singularDirichletResolventToH1_right q a ha g).symm

/-- The generic base resolvent is the exact original compact H-minus-one resolvent. -/
theorem pencilResolvent_singularDirichletPencilEquiv (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) :
    pencilResolvent singularDirichletDomainInclusion.toLinearMap
      (singularDirichletPencilEquiv q a ha).toLinearEquiv =
        (singularDirichletBaseResolvent q a).toLinearMap := by
  apply LinearMap.ext
  intro g
  change singularDirichletDomainInclusion ((singularDirichletPencilEquiv q a ha).symm g) = _
  rw [singularDirichletPencilEquiv_symm]
  rfl

/-- The original physical pencil is exactly the spectral shift of this domain-to-base isomorphism. -/
theorem singularDirichletPencil_eq_resolvent_shift (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) :
    (singularDirichletOperator q -
      z • singularDirichletDomainInclusion).toLinearMap =
      (singularDirichletPencilEquiv q a ha).toLinearMap -
        (z-a) • singularDirichletDomainInclusion.toLinearMap := by
  apply LinearMap.ext
  intro f
  change singularDirichletOperator q f -
    z • singularDirichletDomainInclusion f =
      singularDirichletPencilEquiv q a ha f - (z-a) • singularDirichletDomainInclusion f
  rw [singularDirichletPencilEquiv_apply]
  module

/-- The native positive pencil differs only by a nonzero sign from A-lambda*J. -/
theorem singularDirichletRootSpace_eq_negative_pencil
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) (n : ℕ) :
    singularDirichletRootSpace q z n =
      pencilRootSpace singularDirichletDomainInclusion.toLinearMap
        (singularDirichletOperator q-z • singularDirichletDomainInclusion).toLinearMap n := by
  have he : (singularDirichletPencil q z).toLinearMap =
      (-1:ℂ) • (singularDirichletOperator q-z • singularDirichletDomainInclusion).toLinearMap := by
    apply LinearMap.ext
    intro f
    change z • singularDirichletDomainInclusion f-singularDirichletOperator q f =
      (-1:ℂ) • (singularDirichletOperator q f-z • singularDirichletDomainInclusion f)
    module
  unfold singularDirichletRootSpace
  rw [he, pencilRootSpace_smul _ _ (-1) (by norm_num)]

theorem singularDirichletRootSpaceTop_eq_negative_pencil
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    singularDirichletRootSpaceTop q z =
      pencilRootSpaceTop singularDirichletDomainInclusion.toLinearMap
        (singularDirichletOperator q-z • singularDirichletDomainInclusion).toLinearMap := by
  unfold singularDirichletRootSpaceTop pencilRootSpaceTop
  exact iSup_congr fun n => singularDirichletRootSpace_eq_negative_pencil q z n

/-- Every actual finite physical root-chain level equals the corresponding compact-resolvent generalized eigenspace. -/
theorem singularDirichletRootSpace_eq_resolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) (hza : z ≠ a) (n : ℕ) :
    singularDirichletRootSpace q z n =
      Module.End.genEigenspace (singularDirichletBaseResolvent q a).toLinearMap (z-a)⁻¹ n := by
  rw [singularDirichletRootSpace_eq_negative_pencil, singularDirichletPencil_eq_resolvent_shift q a z ha]
  have h := pencilRootSpace_eq_resolvent_genEigenspace singularDirichletDomainInclusion.toLinearMap
    singularDirichletDomainInclusion_injective (singularDirichletPencilEquiv q a ha).toLinearEquiv
      (z-a) (sub_ne_zero.mpr hza) n
  rwa [pencilResolvent_singularDirichletPencilEquiv] at h

/-- The full physical algebraic root space equals the complete nonzero compact-resolvent generalized eigenspace. -/
theorem singularDirichletRootSpaceTop_eq_resolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) (hza : z ≠ a) :
    singularDirichletRootSpaceTop q z =
      Module.End.genEigenspace (singularDirichletBaseResolvent q a).toLinearMap (z-a)⁻¹ ⊤ := by
  rw [singularDirichletRootSpaceTop_eq_negative_pencil, singularDirichletPencil_eq_resolvent_shift q a z ha]
  have h := pencilRootSpaceTop_eq_resolvent_genEigenspace singularDirichletDomainInclusion.toLinearMap
    singularDirichletDomainInclusion_injective (singularDirichletPencilEquiv q a ha).toLinearEquiv
      (z-a) (sub_ne_zero.mpr hza)
  rwa [pencilResolvent_singularDirichletPencilEquiv] at h

/-- A physical resolvent point has no nonzero actual algebraic root vectors. -/
theorem singularDirichletRootSpaceTop_eq_bot_of_mem_resolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ)
    (hz : z ∈ singularDirichletResolventSet q) :
    singularDirichletRootSpaceTop q z = ⊥ := by
  rw [singularDirichletRootSpaceTop_eq_negative_pencil]
  exact pencilRootSpaceTop_eq_bot_of_injective singularDirichletDomainInclusion.toLinearMap
    (singularDirichletOperator q -
      z • singularDirichletDomainInclusion).toLinearMap hz.1

/-- Full physical algebraic root spaces are finite dimensional at every complex parameter. -/
theorem finiteDimensional_singularDirichletRootSpaceTop (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    FiniteDimensional ℂ (singularDirichletRootSpaceTop
      q z) := by
  obtain ⟨a,ha⟩ := singularDirichletResolventSet_nonempty q
  by_cases hza : z = a
  · subst z
    rw [singularDirichletRootSpaceTop_eq_bot_of_mem_resolvent q a ha]
    infer_instance
  · rw [singularDirichletRootSpaceTop_eq_resolvent q a z ha hza]
    exact CompactSpectrum.finiteDimensional_genEigenspace_top
      (singularDirichletBaseResolvent q a) (isCompactOperator_singularDirichletBaseResolvent q a)
        (inv_ne_zero (sub_ne_zero.mpr hza))

/-- The full physical algebraic root space is attained at a finite chain length. -/
theorem exists_singularDirichletRootSpace_eq_top (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    ∃ N : ℕ, singularDirichletRootSpace q z N =
      singularDirichletRootSpaceTop q z := by
  obtain ⟨a,ha⟩ := singularDirichletResolventSet_nonempty q
  by_cases hza : z = a
  · subst z
    refine ⟨0,?_⟩
    rw [singularDirichletRootSpaceTop_eq_bot_of_mem_resolvent q a ha]
    rfl
  · obtain ⟨N,hN⟩ := CompactSpectrum.exists_genEigenspace_eq_top
      (singularDirichletBaseResolvent q a) (isCompactOperator_singularDirichletBaseResolvent q a)
        (inv_ne_zero (sub_ne_zero.mpr hza))
    exact ⟨N,by rw [singularDirichletRootSpace_eq_resolvent q a z ha hza,
      singularDirichletRootSpaceTop_eq_resolvent q a z ha hza]; exact hN⟩

/-- The actual finite physical algebraic multiplicity, defined from the full original root space. -/
def singularDirichletAlgebraicMultiplicity (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) : ℕ :=
  letI := finiteDimensional_singularDirichletRootSpaceTop q z
  Module.finrank ℂ (singularDirichletRootSpaceTop q z)

/-- Actual algebraic multiplicity equals that of any actual compact resolvent at the transformed value. -/
theorem singularDirichletAlgebraicMultiplicity_eq_resolvent (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (a z : ℂ)
    (ha : a ∈ singularDirichletResolventSet q) (hza : z ≠ a) :
    singularDirichletAlgebraicMultiplicity q z = Module.finrank ℂ
      (Module.End.genEigenspace (singularDirichletBaseResolvent q a).toLinearMap (z-a)⁻¹ ⊤) := by
  unfold singularDirichletAlgebraicMultiplicity
  rw [singularDirichletRootSpaceTop_eq_resolvent q a z ha hza]

/-- The eventual finite root-chain levels all equal the full physical algebraic root space. -/
theorem singularDirichletRootSpace_stabilizes (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      singularDirichletRootSpace q z n =
        singularDirichletRootSpaceTop q z := by
  obtain ⟨N,hN⟩ := exists_singularDirichletRootSpace_eq_top q z
  refine ⟨N,fun n hn => le_antisymm ?_ ?_⟩
  · exact le_iSup (fun n => singularDirichletRootSpace
      q z n) n
  · rw [← hN]
    exact pencilRootSpace_mono _ _ hn

/-- Actual physical algebraic multiplicity is positive exactly on the actual physical spectrum. -/
theorem singularDirichletAlgebraicMultiplicity_pos_iff (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    0 < singularDirichletAlgebraicMultiplicity q z ↔ z ∈ singularDirichletSpectrum q := by
  let := finiteDimensional_singularDirichletRootSpaceTop q z
  constructor
  · intro h
    by_contra hnot
    have hz : z ∈ singularDirichletResolventSet q := by
      simpa only [singularDirichletSpectrum, Set.mem_compl_iff, not_not] using hnot
    unfold singularDirichletAlgebraicMultiplicity at h
    rw [singularDirichletRootSpaceTop_eq_bot_of_mem_resolvent q z hz, finrank_bot] at h
    exact Nat.not_lt_zero _ h
  · intro hz
    obtain ⟨f,hf0,hf⟩ := (mem_singularDirichletSpectrum_iff q z).mp hz
    have hlevel : singularDirichletDomainInclusion f ∈ singularDirichletRootSpace q z 1 := by
      apply (mem_singularDirichletRootSpace_succ q z 0 _).mpr
      refine ⟨f, rfl, ?_⟩
      change singularDirichletPencil q z f = 0
      exact (singularDirichletPencil_eq_zero_iff q z f).mpr hf
    have htop : singularDirichletDomainInclusion f ∈ singularDirichletRootSpaceTop q z :=
      (le_iSup (fun n => singularDirichletRootSpace q z n) 1) hlevel
    change 0 < Module.finrank ℂ (singularDirichletRootSpaceTop
      q z)
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨singularDirichletDomainInclusion f,htop⟩,?_⟩
    intro he
    apply hf0
    apply singularDirichletDomainInclusion_injective
    have h := congrArg Subtype.val he
    change singularDirichletDomainInclusion f = (0 : UnitDirichletHminus) at h
    simpa only [map_zero] using h


/-- Actual finite algebraic multiplicity is supported exactly on the independently
normalized complex characteristic zero set. This does not identify its value with zero order. -/
theorem singularDirichletAlgebraicMultiplicity_pos_iff_characteristic
    (q : PeriodOneHminusOne) (z : ℂ) :
    0 < singularDirichletAlgebraicMultiplicity (periodOneOriginal q) z ↔
      hillHminusDirichlet q z = 0 :=
  (singularDirichletAlgebraicMultiplicity_pos_iff (periodOneOriginal q) z).trans
    (mem_singularDirichletSpectrum_source_iff q z)

/-- Away from the full spectrum the actual algebraic multiplicity is zero, and conversely. -/
theorem singularDirichletAlgebraicMultiplicity_eq_zero_iff_resolvent
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (z : ℂ) :
    singularDirichletAlgebraicMultiplicity q z = 0 ↔ z ∈ singularDirichletResolventSet q := by
  constructor
  · intro hz
    by_contra hn
    have hp := (singularDirichletAlgebraicMultiplicity_pos_iff q z).mpr hn
    rw [hz] at hp
    exact Nat.not_lt_zero _ hp
  · intro hz
    apply Nat.eq_zero_of_not_pos
    intro hp
    exact ((singularDirichletAlgebraicMultiplicity_pos_iff q z).mp hp) hz

end NLS.KdV
