import NLS.ZakharovShabat.IntervalL2Isomorphism
import NLS.ZakharovShabat.ClassicalIntervalIsomorphism
import NLS.ZakharovShabat.ClassicalIntervalEigenvalues

/-!
# The original classical interval operator

The domain is the original endpoint subspace with its physical `H¹` norm, and
the base space is the original component-sum `L²` space. Transport constructs
bounded inclusion and operator maps. Their physical realization is proved for
arbitrary original representatives, using the actual differential expression.
-/

noncomputable section
open MeasureTheory Set NLS.Fourier
namespace NLS.ZakharovShabat

/-- The physical differential expression only uses interval values and the a.e. potential. -/
theorem physicalOperator_congr_on_interval {a c : ℝ} {φ ψ f g : ℝ → ℂ × ℂ}
    (hφ : φ =ᵐ[volume.restrict (Ioc a c)] ψ) (hf : EqOn f g (Icc a c)) :
    physicalOperator φ f =ᵐ[volume.restrict (Ioc a c)] physicalOperator ψ g := by
  have h₁ : EqOn (fun x => (f x).1) (fun x => (g x).1) (Ioo a c) :=
    fun x hx => congrArg Prod.fst (hf (Ioo_subset_Icc_self hx))
  have h₂ : EqOn (fun x => (f x).2) (fun x => (g x).2) (Ioo a c) :=
    fun x hx => congrArg Prod.snd (hf (Ioo_subset_Icc_self hx))
  have hm : ∀ᵐ x : ℝ ∂volume.restrict (Ioc a c), x ∈ Ioo a c := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [volume.ae_ne c] with x hne hx
    exact ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩
  filter_upwards [hφ, hm] with x hx hmem
  dsimp only [physicalOperator]
  rw [h₁.deriv isOpen_Ioo hmem, h₂.deriv isOpen_Ioo hmem, hx, hf (Ioo_subset_Icc_self hmem)]

namespace BoundaryCondition

/-- The coefficient operator restricted to the selected boundary summands. -/
def operatorToBoundary (b : BoundaryCondition) (u : IntervalPairL2) :
    domain (p := 2) b →L[ℂ] space (p := 2) b :=
  ((operator (by simp) (intervalPotentialCoefficients u)).comp (domain b).subtypeL).codRestrict _
    (fun a => operator_mem b (by simp) _ (intervalPotentialToDirichlet u).property a.val a.property)

@[simp] theorem operatorToBoundary_apply (b : BoundaryCondition) (u : IntervalPairL2) (a : domain (p := 2) b) :
    (operatorToBoundary b u a).val = operator (by simp) (intervalPotentialCoefficients u) a.val := rfl

/-- Original physical domain inclusion, bounded for the classical `H¹` norm. -/
def classicalInclusion (b : BoundaryCondition) : ClassicalIntervalDomain b →L[ℂ] IntervalPairL2 :=
  (intervalL2Equiv b).symm.toContinuousLinearMap.comp
    ((inclusion b).comp (classicalIntervalEquiv b).toContinuousLinearMap)

/-- The original interval operator with its actual classical domain and physical base space. -/
def classicalOperator (b : BoundaryCondition) (u : IntervalPairL2) :
    ClassicalIntervalDomain b →L[ℂ] IntervalPairL2 :=
  (intervalL2Equiv b).symm.toContinuousLinearMap.comp
    ((operatorToBoundary b u).comp (classicalIntervalEquiv b).toContinuousLinearMap)

@[simp] theorem intervalL2Equiv_classicalInclusion (b : BoundaryCondition) (f : ClassicalIntervalDomain b) :
    intervalL2Equiv b (classicalInclusion b f) = inclusion b (classicalIntervalEquiv b f) :=
  (intervalL2Equiv b).apply_symm_apply _

@[simp] theorem intervalL2Equiv_classicalOperator (b : BoundaryCondition) (u : IntervalPairL2)
    (f : ClassicalIntervalDomain b) :
    intervalL2Equiv b (classicalOperator b u f) = operatorToBoundary b u (classicalIntervalEquiv b f) :=
  (intervalL2Equiv b).apply_symm_apply _

theorem classicalInclusion_injective (b : BoundaryCondition) : Function.Injective (classicalInclusion b) := by
  intro f g h
  apply (classicalIntervalEquiv b).injective
  apply Subtype.ext
  apply domainInclusion_injective
  have he := congrArg (intervalL2Equiv b) h
  simp only [intervalL2Equiv_classicalInclusion] at he
  exact congrArg Subtype.val he

theorem classicalInclusion_denseRange (b : BoundaryCondition) : DenseRange (classicalInclusion b) :=
  (intervalL2Equiv b).symm.surjective.denseRange.comp
    ((inclusion_denseRange b (by simp)).comp (classicalIntervalEquiv b).surjective.denseRange (inclusion b).continuous)
    (intervalL2Equiv b).symm.continuous

/-- Classical representatives are square integrable in the original interval sense. -/
theorem memLp_classicalDomainRepresentative (b : BoundaryCondition) (f : ClassicalIntervalDomain b) :
    MemLp (classicalDomainRepresentative b f) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_classicalIntervalRestriction b (classicalIntervalEquiv b f).val (classicalIntervalEquiv b f).property

/-- Inclusion is precisely passage from the actual classical function to its physical `L²` class. -/
theorem classicalInclusion_representative (b : BoundaryCondition) (f : ClassicalIntervalDomain b) :
    classicalInclusion b f = intervalL2OfFunction (classicalDomainRepresentative b f)
      (memLp_classicalDomainRepresentative b f) := intervalL2Equiv_symm_inclusion b (classicalIntervalEquiv b f)

/-- The original function is unchanged by domain inclusion. -/
theorem classicalInclusion_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) (hL : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    classicalInclusion b (classicalDomainOfFunction b f hf) = intervalL2OfFunction f hL := by
  rw [classicalInclusion_representative]
  apply (intervalL2OfFunction_eq_iff _ _ _ _).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact classicalDomainRepresentative_apply b (classicalDomainOfFunction b f hf) ⟨x, Ioc_subset_Icc_self hx⟩

/-- Transported operator values realize the actual original differential expression almost everywhere. -/
theorem classicalOperator_realization (b : BoundaryCondition) (u : IntervalPairL2) (f : ClassicalIntervalDomain b) :
    intervalL2Representative (classicalOperator b u f) =ᵐ[volume.restrict (Ioc 0 1)]
      physicalOperator (intervalL2Representative u) (classicalDomainRepresentative b f) := by
  have hR := intervalL2Equiv_symm_restrict b (operatorToBoundary b u (classicalIntervalEquiv b f))
  have hO := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (show (1 : ℝ) ≤ 2 by norm_num))
    (physical_operator_realization (intervalPotentialCoefficients u) (classicalIntervalEquiv b f).val)
  have hP := physicalBase_dirichletPotentialCoefficients_restrict (intervalL2Representative u)
    (memLp_intervalL2Representative u)
  filter_upwards [hR, hO, hP] with x hr ho hp
  change _ = physicalOperator (intervalL2Representative u) (physicalDomain (classicalIntervalEquiv b f).val) x
  change intervalL2Representative (classicalOperator b u f) x =
    physicalBase (operator (by simp) (intervalPotentialCoefficients u) (classicalIntervalEquiv b f).val) x at hr
  change physicalBase (intervalPotentialCoefficients u) x = intervalL2Representative u x at hp
  rw [hr, ho]
  dsimp only [physicalOperator]
  rw [hp]

/-- The physical action is independent of the representatives chosen for the original input. -/
theorem classicalOperator_realization_ofFunction (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalIntervalDomain b f) :
    intervalL2Representative (classicalOperator b (intervalL2OfFunction φ hφ) (classicalDomainOfFunction b f hf))
      =ᵐ[volume.restrict (Ioc 0 1)] physicalOperator φ f := by
  apply (classicalOperator_realization b _ _).trans
  apply physicalOperator_congr_on_interval (intervalL2Representative_ofFunction φ hφ)
  intro x hx
  exact classicalDomainRepresentative_apply b (classicalDomainOfFunction b f hf) ⟨x, hx⟩

/-- Every original classical operator output is square integrable. -/
theorem memLp_classicalOperator_ofFunction (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalIntervalDomain b f) :
    MemLp (physicalOperator φ f) 2 (volume.restrict (Ioc 0 1)) :=
  (memLp_congr_ae (classicalOperator_realization_ofFunction b φ f hφ hf)).mp (memLp_intervalL2Representative _)

/-- Exact equality with the physical `L²` class of the original differential expression. -/
theorem classicalOperator_ofFunction (b : BoundaryCondition) (φ f : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hf : HasClassicalIntervalDomain b f) :
    classicalOperator b (intervalL2OfFunction φ hφ) (classicalDomainOfFunction b f hf) =
      intervalL2OfFunction (physicalOperator φ f) (memLp_classicalOperator_ofFunction b φ f hφ hf) := by
  apply intervalL2Representative_injective
  exact (classicalOperator_realization_ofFunction b φ f hφ hf).trans (intervalL2Representative_ofFunction _ _).symm

end BoundaryCondition
end NLS.ZakharovShabat
