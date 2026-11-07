import NLS.KdV.SingularDirichletFreeIsomorphism
import NLS.KdV.SingularDirichletCharacteristicSufficiency
import NLS.KdV.SingularHillFredholm

/-! # Full native Dirichlet Fredholm alternative

The verified massive free Dirichlet isomorphism normalizes every original
complex singular potential to identity plus compact on the complete native
H1 domain. The full H-minus-one pencil is bijective exactly off its native
point eigenvalues, and hence exactly off the normalized characteristic zeros
for the entire original complex unit-period source.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The actual singular multiplication, with every native zero-trace test retained. -/
def singularDirichletMultiplication (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    UnitDirichletH1 →L[ℂ] UnitDirichletHminus :=
  singularDirichletRestriction.comp ((hminusOneMultiplication q).comp unitDirichletOriginalH1)

/-- The unchanged native domain inclusion is compact in the full native base norm. -/
theorem isCompactOperator_singularDirichletDomainInclusion :
    IsCompactOperator singularDirichletDomainInclusion :=
  (isCompactOperator_singularHillDomainInclusion.comp_clm unitDirichletOriginalH1).clm_comp
    singularDirichletRestriction

/-- Every original H-minus-one potential gives a compact native singular multiplier. -/
theorem isCompactOperator_singularDirichletMultiplication
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    IsCompactOperator (singularDirichletMultiplication q) :=
  ((isCompactOperator_hminusOneMultiplication q).comp_clm unitDirichletOriginalH1).clm_comp
    singularDirichletRestriction

theorem singularDirichletOperator_eq_free_add (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    singularDirichletOperator q = singularDirichletOperator 0+singularDirichletMultiplication q := by
  apply ContinuousLinearMap.ext
  intro f
  change singularDirichletRestriction (singularHillOperator q (unitDirichletOriginalH1 f)) =
    singularDirichletRestriction (singularHillOperator 0 (unitDirichletOriginalH1 f))+
      singularDirichletRestriction (hminusOneMultiplication q (unitDirichletOriginalH1 f))
  rw [singularHillOperator_zero]
  exact singularDirichletRestriction.map_add _ _

/-- Fixed free normalization of the complete native Dirichlet pencil. -/
def singularDirichletNormalizedPencil (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    UnitDirichletH1 →L[ℂ] UnitDirichletH1 :=
  singularDirichletFreeIsomorphism.symm.toContinuousLinearMap.comp
    (singularDirichletOperator q-lambda • singularDirichletDomainInclusion)

/-- The full native H-minus-one pencil resolvent, with its original H1 domain. -/
def singularDirichletResolventSet (q : FourierLebesgueSpace (2:ℝ) (-1) 2) : Set ℂ :=
  {lambda | Function.Bijective (singularDirichletOperator q-lambda • singularDirichletDomainInclusion)}

/-- Free normalization preserves exactly the entire native resolvent set. -/
theorem mem_singularDirichletResolventSet_iff_isUnit
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    lambda ∈ singularDirichletResolventSet q ↔ IsUnit (singularDirichletNormalizedPencil q lambda) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  change Function.Bijective (singularDirichletOperator q-lambda • singularDirichletDomainInclusion) ↔
    Function.Bijective (singularDirichletNormalizedPencil q lambda)
  constructor
  · intro h
    exact singularDirichletFreeIsomorphism.symm.bijective.comp h
  · intro h
    constructor
    · intro f g hfg
      apply h.1
      exact congrArg singularDirichletFreeIsomorphism.symm hfg
    · intro F
      obtain ⟨f, hf⟩ := h.2 (singularDirichletFreeIsomorphism.symm F)
      exact ⟨f, singularDirichletFreeIsomorphism.symm.injective hf⟩

theorem singularDirichletNormalizedPencil_sub_one
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    singularDirichletNormalizedPencil q lambda-1 =
      singularDirichletFreeIsomorphism.symm.toContinuousLinearMap.comp
        (singularDirichletMultiplication q-(lambda+1) • singularDirichletDomainInclusion) := by
  apply ContinuousLinearMap.ext
  intro f
  change singularDirichletFreeIsomorphism.symm
    (singularDirichletOperator q f-lambda • singularDirichletDomainInclusion f)-f =
      singularDirichletFreeIsomorphism.symm
        (singularDirichletMultiplication q f-(lambda+1) • singularDirichletDomainInclusion f)
  have hid := singularDirichletFreeIsomorphism_symm_left f
  calc
    _ = singularDirichletFreeIsomorphism.symm
        (singularDirichletOperator q f-lambda • singularDirichletDomainInclusion f)-
      singularDirichletFreeIsomorphism.symm
        (singularDirichletOperator 0 f+singularDirichletDomainInclusion f) := by rw [hid]
    _ = singularDirichletFreeIsomorphism.symm
      ((singularDirichletOperator q f-lambda • singularDirichletDomainInclusion f)-
        (singularDirichletOperator 0 f+singularDirichletDomainInclusion f)) := (map_sub _ _ _).symm
    _ = _ := by
      congr 1
      rw [singularDirichletOperator_eq_free_add]
      change ((singularDirichletOperator 0 f+singularDirichletMultiplication q f)-
        lambda • singularDirichletDomainInclusion f)-
          (singularDirichletOperator 0 f+singularDirichletDomainInclusion f) = _
      module

/-- Every normalized native pencil is identity plus a compact operator. -/
theorem isCompactOperator_singularDirichletNormalizedPencil_sub_one
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    IsCompactOperator (singularDirichletNormalizedPencil q lambda-1 : UnitDirichletH1 →L[ℂ] UnitDirichletH1) := by
  rw [singularDirichletNormalizedPencil_sub_one]
  exact ((isCompactOperator_singularDirichletMultiplication q).sub
    (isCompactOperator_singularDirichletDomainInclusion.smul (lambda+1))).clm_comp
      singularDirichletFreeIsomorphism.symm.toContinuousLinearMap

/-- Fredholm index zero on the entire original native domain. -/
theorem singularDirichletNormalizedPencil_fredholm_index_zero
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    (singularDirichletNormalizedPencil q lambda).IsFredholm ∧
      Module.finrank ℂ (singularDirichletNormalizedPencil q lambda).ker =
        Module.finrank ℂ (UnitDirichletH1 ⧸ (singularDirichletNormalizedPencil q lambda).range) :=
  CompactSpectrum.fredholm_index_zero_of_compact_sub_smul _ (by norm_num : (1:ℂ) ≠ 0)
    (by simpa only [one_smul] using isCompactOperator_singularDirichletNormalizedPencil_sub_one q lambda)

theorem singularDirichletNormalizedPencil_bijective_of_injective
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ)
    (hi : Function.Injective (singularDirichletNormalizedPencil q lambda)) :
    Function.Bijective (singularDirichletNormalizedPencil q lambda) :=
  CompactScalarPerturbation.bijective_of_injective _ (by norm_num : (1:ℂ) ≠ 0)
    (by simpa only [one_smul] using isCompactOperator_singularDirichletNormalizedPencil_sub_one q lambda) hi

theorem singularDirichletNormalizedPencil_apply_eq_zero_iff
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) (f : UnitDirichletH1) :
    singularDirichletNormalizedPencil q lambda f = 0 ↔
      singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f := by
  constructor
  · intro h
    have he := congrArg singularDirichletFreeIsomorphism h
    change singularDirichletFreeIsomorphism
      (singularDirichletFreeIsomorphism.symm
        (singularDirichletOperator q f-lambda • singularDirichletDomainInclusion f)) =
      singularDirichletFreeIsomorphism 0 at he
    rw [ContinuousLinearEquiv.apply_symm_apply, map_zero] at he
    exact sub_eq_zero.mp he
  · intro h
    change singularDirichletFreeIsomorphism.symm
      (singularDirichletOperator q f-lambda • singularDirichletDomainInclusion f) = 0
    rw [h, sub_self, map_zero]

/-- There is no failure of native pencil invertibility other than a genuine eigenvector. -/
theorem not_mem_singularDirichletResolventSet_iff
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ) :
    lambda ∉ singularDirichletResolventSet q ↔ ∃ f : UnitDirichletH1, f ≠ 0 ∧
      singularDirichletOperator q f = lambda • singularDirichletDomainInclusion f := by
  rw [mem_singularDirichletResolventSet_iff_isUnit, ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · intro h
    by_contra hn
    apply h
    apply singularDirichletNormalizedPencil_bijective_of_injective q lambda
    intro f g hfg
    apply sub_eq_zero.mp
    have hz : singularDirichletNormalizedPencil q lambda (f-g) = 0 := by rw [map_sub,hfg,sub_self]
    by_contra hne
    exact hn ⟨f-g,hne,(singularDirichletNormalizedPencil_apply_eq_zero_iff q lambda (f-g)).mp hz⟩
  · rintro ⟨f, hf, he⟩ h
    apply hf
    exact h.1 (((singularDirichletNormalizedPencil_apply_eq_zero_iff q lambda f).mpr he).trans (map_zero _).symm)

/-- EVERY complex source potential has native pencil resolvent exactly away
from the independently normalized scalar characteristic zeros. -/
theorem mem_singularDirichletResolventSet_source_iff (q : PeriodOneHminusOne) (lambda : ℂ) :
    lambda ∈ singularDirichletResolventSet (periodOneOriginal q) ↔ hillHminusDirichlet q lambda ≠ 0 := by
  simpa only [not_not] using not_congr
    ((not_mem_singularDirichletResolventSet_iff (periodOneOriginal q) lambda).trans
      (hillHminusDirichlet_eq_zero_iff_native_eigen q lambda).symm)

end NLS.KdV
