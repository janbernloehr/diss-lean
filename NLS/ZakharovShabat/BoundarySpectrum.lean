import NLS.ZakharovShabat.BoundaryResolvent
import NLS.ZakharovShabat.PeriodicSpectrum

/-!
# Spectra of the Dirichlet and Neumann restrictions

Chapter 1, §4, proof of Theorem 1.4. The periodic pencil is the direct sum of
the two boundary pencils. Its spectrum is therefore their union. Each boundary
spectrum is closed and discrete, with only finitely many points in bounded
sets. These statements concern already-reflected coefficient potentials.
-/

open scoped ENNReal
noncomputable section
namespace NLS.ZakharovShabat
namespace BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (b : BoundaryCondition)

/-- The spectrum of the actual boundary restriction. -/
def spectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) : Set ℂ :=
  (resolventSet b hp φ hφ)ᶜ

theorem spectrum_subset_periodic (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) : spectrum b hp φ hφ ⊆ periodicSpectrum hp φ :=
  fun z hz hw => hz (mem_resolventSet_of_periodic b hp φ hφ z hw)

theorem isClosed_spectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) :
    IsClosed (spectrum b hp φ hφ) := (isOpen_resolventSet b hp φ hφ).isClosed_compl

theorem finite_spectrum_inter_of_isBounded (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) {K : Set ℂ} (hK : Bornology.IsBounded K) :
    Set.Finite (spectrum b hp φ hφ ∩ K) :=
  (finite_periodicSpectrum_inter_of_isBounded hp φ hK).subset
    (Set.inter_subset_inter_left K (spectrum_subset_periodic b hp φ hφ))

theorem discreteTopology_spectrum (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) : DiscreteTopology (spectrum b hp φ hφ) := by
  apply continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact
  rw [tendsto_cofinite_cocompact_iff]
  intro K hK
  exact Set.Finite.of_injOn
    (fun z hz => show (z : ℂ) ∈ spectrum b hp φ hφ ∩ K from ⟨z.property, hz⟩)
    (fun _ _ _ _ h => Subtype.ext h) (finite_spectrum_inter_of_isBounded b hp φ hφ hK.isBounded)

theorem domainProjection_eq_of_pencil_eq (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∈ resolventSet b hp φ hφ)
    (f g : Domain p) (h : spectralPencil hp φ z f = spectralPencil hp φ z g) :
    domainProjection b f = domainProjection b g := by
  have he : pencil b hp φ hφ z (domainRetract b f) = pencil b hp φ hφ z (domainRetract b g) := by
    apply Subtype.ext
    change spectralPencil hp φ z (domainProjection b f) = spectralPencil hp φ z (domainProjection b g)
    rw [spectralPencil_projection b hp φ hφ, spectralPencil_projection b hp φ hφ, h]
  exact congrArg Subtype.val (hz.injective he)

/-- Changing the spectral parameter only changes the scalar inclusion term. -/
theorem pencil_sub_parameter (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (w z : ℂ) :
    pencil b hp φ hφ z = pencil b hp φ hφ w + (z - w) • inclusion b := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change z • domainInclusion f.val - operator hp φ f.val =
    (w • domainInclusion f.val - operator hp φ f.val) + (z - w) • domainInclusion f.val
  module

theorem pencil_comp_resolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (w z : ℂ) (hw : w ∈ resolventSet b hp φ hφ) :
    (pencil b hp φ hφ z).comp (resolventToDomain b hp φ hφ w) =
      1 + (z - w) • resolvent b hp φ hφ w := by
  rw [pencil_sub_parameter b hp φ hφ w z, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.smul_comp]
  have he : (pencil b hp φ hφ w).comp (resolventToDomain b hp φ hφ w) = 1 := by
    apply ContinuousLinearMap.ext
    intro a
    exact pencil_resolventToDomain b hp φ hφ w hw a
  rw [he]
  rfl

theorem mem_resolventSet_iff_shift_isUnit (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (w z : ℂ) (hw : w ∈ resolventSet b hp φ hφ) :
    z ∈ resolventSet b hp φ hφ ↔ IsUnit (1 + (z - w) • resolvent b hp φ hφ w) := by
  have hR : Function.Bijective (resolventToDomain b hp φ hφ w) :=
    ⟨Function.LeftInverse.injective (pencil_resolventToDomain b hp φ hφ w hw),
      Function.RightInverse.surjective (resolventToDomain_pencil b hp φ hφ w hw)⟩
  rw [← pencil_comp_resolventToDomain b hp φ hφ w z hw, ContinuousLinearMap.isUnit_iff_bijective]
  exact (Function.Bijective.of_comp_iff (pencil b hp φ hφ z) hR).symm

/-- Nonzero spectral transformation to the compact boundary resolvent. -/
theorem mem_spectrum_iff_resolvent_spectrum (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (w z : ℂ) (hw : w ∈ resolventSet b hp φ hφ) (hzw : z ≠ w) :
    z ∈ spectrum b hp φ hφ ↔ (w - z)⁻¹ ∈ _root_.spectrum ℂ (resolvent b hp φ hφ w) := by
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hzw.symm
  let u : (↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b))ˣ :=
    { val := (w - z) • 1
      inv := (w - z)⁻¹ • 1
      val_inv := by
        apply ContinuousLinearMap.ext
        intro a
        change (w - z) • ((w - z)⁻¹ • a) = a
        exact smul_inv_smul₀ hwz a
      inv_val := by
        apply ContinuousLinearMap.ext
        intro a
        change (w - z)⁻¹ • ((w - z) • a) = a
        exact inv_smul_smul₀ hwz a }
  have he : 1 + (z - w) • resolvent b hp φ hφ w =
      u.val * ((w - z)⁻¹ • 1 - resolvent b hp φ hφ w) := by
    apply ContinuousLinearMap.ext
    intro a
    change a + (z - w) • resolvent b hp φ hφ w a =
      (w - z) • ((w - z)⁻¹ • a - resolvent b hp φ hφ w a)
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hwz, one_smul]
    module
  change ¬ z ∈ resolventSet b hp φ hφ ↔ _
  rw [mem_resolventSet_iff_shift_isUnit b hp φ hφ w z hw, he,
    Units.isUnit_units_mul, _root_.spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]

/-- The compact resolvent rules out residual or continuous boundary spectrum. -/
theorem mem_spectrum_iff_exists_kernel (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) : z ∈ spectrum b hp φ hφ ↔
    ∃ f : domain (p := p) b, f ≠ 0 ∧ pencil b hp φ hφ z f = 0 := by
  constructor
  · intro hz
    obtain ⟨w, hw₀⟩ := ZakharovShabat.resolventSet_nonempty hp φ
    have hw := mem_resolventSet_of_periodic b hp φ hφ w hw₀
    have hzw : z ≠ w := by rintro rfl; exact hz hw
    have hwz : w - z ≠ 0 := sub_ne_zero.mpr hzw.symm
    obtain ⟨a, ha⟩ := ((isCompactOperator_resolvent b hp φ hφ w).hasEigenvalue_iff_mem_spectrum
      (inv_ne_zero hwz) |>.mpr
        ((mem_spectrum_iff_resolvent_spectrum b hp φ hφ w z hw hzw).mp hz)).exists_hasEigenvector
    refine ⟨resolventToDomain b hp φ hφ w a, ?_, ?_⟩
    · intro hf
      have h := pencil_resolventToDomain b hp φ hφ w hw a
      rw [hf, map_zero] at h
      exact ha.2 h.symm
    · have h := congrArg (fun A : ↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b) => A a)
        (pencil_comp_resolventToDomain b hp φ hφ w z hw)
      change pencil b hp φ hφ z (resolventToDomain b hp φ hφ w a) =
        a + (z - w) • resolvent b hp φ hφ w a at h
      have heigen : resolvent b hp φ hφ w a = (w - z)⁻¹ • a := ha.apply_eq_smul
      rw [heigen, smul_smul] at h
      have he : (z - w) * (w - z)⁻¹ = -1 := by
        rw [show z - w = -(w - z) by ring, neg_mul, mul_inv_cancel₀ hwz]
      simpa [he] using h
  · rintro ⟨f, hf, he⟩ hz
    exact hf (hz.injective (he.trans (map_zero _).symm))

/-- Each boundary spectral point has an eigenvector satisfying that boundary condition. -/
theorem mem_spectrum_iff_exists_eigenvector (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) : z ∈ spectrum b hp φ hφ ↔
    ∃ f : Domain p, f ∈ domain b ∧ f ≠ 0 ∧ operator hp φ f = z • domainInclusion f := by
  rw [mem_spectrum_iff_exists_kernel]
  constructor
  · rintro ⟨f, hf, he⟩
    refine ⟨f.val, f.property, fun h => hf (Subtype.ext h), ?_⟩
    have h := congrArg Subtype.val he
    change z • domainInclusion f.val - operator hp φ f.val = 0 at h
    exact (sub_eq_zero.mp h).symm
  · rintro ⟨f, hf, hne, he⟩
    refine ⟨⟨f, hf⟩, fun h => hne (congrArg Subtype.val h), ?_⟩
    apply Subtype.ext
    change z • domainInclusion f - operator hp φ f = 0
    rw [he, sub_self]

end BoundaryCondition

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Invertibility of the periodic pencil is exactly invertibility of both boundary pencils. -/
theorem mem_periodicResolventSet_iff_boundary (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    z ∈ resolventSet hp φ ↔
      z ∈ BoundaryCondition.resolventSet .dirichlet hp φ hφ ∧
      z ∈ BoundaryCondition.resolventSet .neumann hp φ hφ := by
  constructor
  · intro hz
    exact ⟨BoundaryCondition.mem_resolventSet_of_periodic _ hp φ hφ z hz,
      BoundaryCondition.mem_resolventSet_of_periodic _ hp φ hφ z hz⟩
  · rintro ⟨hd, hn⟩
    constructor
    · intro f g h
      have hD := BoundaryCondition.domainProjection_eq_of_pencil_eq .dirichlet hp φ hφ z hd f g h
      have hN := BoundaryCondition.domainProjection_eq_of_pencil_eq .neumann hp φ hφ z hn f g h
      calc
        f = domainDirichletProjection f + domainNeumannProjection f :=
          (ReflectionSplit.decomposition _ f).symm
        _ = domainDirichletProjection g + domainNeumannProjection g := congrArg₂ (· + ·) hD hN
        _ = g := ReflectionSplit.decomposition _ g
    · intro a
      obtain ⟨f, hf⟩ := hd.surjective (BoundaryCondition.retract .dirichlet a)
      obtain ⟨g, hg⟩ := hn.surjective (BoundaryCondition.retract .neumann a)
      refine ⟨f.val + g.val, ?_⟩
      have hf' := congrArg Subtype.val hf
      have hg' := congrArg Subtype.val hg
      change spectralPencil hp φ z f.val = dirichletProjection a at hf'
      change spectralPencil hp φ z g.val = neumannProjection a at hg'
      rw [map_add, hf', hg', dirichlet_neumann_decomposition]

/-- The periodic spectrum splits into the actual Dirichlet and Neumann spectra. -/
theorem periodicSpectrum_eq_boundary_union (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) :
    periodicSpectrum hp φ = BoundaryCondition.spectrum .dirichlet hp φ hφ ∪
      BoundaryCondition.spectrum .neumann hp φ hφ := by
  ext z
  change ¬ z ∈ resolventSet hp φ ↔
    (¬ z ∈ BoundaryCondition.resolventSet .dirichlet hp φ hφ) ∨
    (¬ z ∈ BoundaryCondition.resolventSet .neumann hp φ hφ)
  rw [mem_periodicResolventSet_iff_boundary hp φ hφ z, not_and_or]

end NLS.ZakharovShabat
