import NLS.ZakharovShabat.ClassicalIntervalSpace
import NLS.Fourier.SobolevEnergyEmbedding

/-!
# The classical boundary-domain isomorphisms (Lemma 4.2)

The original interval domains carry their exact physical, component-sum `H¹`
norm. Signed extension is a continuous linear equivalence onto the corresponding
weighted boundary domain. Its inverse is physical restriction, and both spaces
are complete. No spectral intertwining is asserted here.
-/

noncomputable section
open Set NLS.Fourier
namespace NLS.ZakharovShabat.BoundaryCondition

private theorem fst_injective (b : BoundaryCondition) :
    Function.Injective (fun a : ↥(domain (p := 2) b) => a.val.1) := by
  intro a c h
  dsimp only at h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [norm_eq_fst_of_mem_domain b _ ((domain b).sub_mem a.property c.property)]
  change ‖a.val.1 - c.val.1‖ = 0
  rw [h, sub_self, norm_zero]

/-- The physical function/derivative Hilbert embedding of the interval domain. -/
private def intervalEnergyEmbedding (b : BoundaryCondition) :
    ClassicalIntervalDomain b →ₗ[ℂ] WithLp 2 (CircleL2 × CircleL2) :=
  sobolevEnergyEmbedding.comp ((LinearMap.fst ℂ (ScalarDomain 2) (ScalarDomain 2)).comp
    ((domain (p := 2) b).subtype.comp (classicalRestrictionLinearEquiv b).symm.toLinearMap))

private theorem intervalEnergyEmbedding_injective (b : BoundaryCondition) :
    Function.Injective (intervalEnergyEmbedding b) := by
  intro u v h
  apply (classicalRestrictionLinearEquiv b).symm.injective
  apply fst_injective b
  exact sobolevEnergyEmbedding_injective h

instance (b : BoundaryCondition) : NormedAddCommGroup (ClassicalIntervalDomain b) :=
  NormedAddCommGroup.induced _ _ (intervalEnergyEmbedding b) (intervalEnergyEmbedding_injective b)

instance (b : BoundaryCondition) : NormedSpace ℂ (ClassicalIntervalDomain b) :=
  NormedSpace.induced ℂ _ _ (intervalEnergyEmbedding b)

/-- The constructed norm is exactly the physical `H¹` norm of the interval representative. -/
theorem norm_classicalDomainRepresentative (b : BoundaryCondition) (u : ClassicalIntervalDomain b) :
    ‖u‖ = classicalIntervalNorm (classicalDomainRepresentative b u) := by
  let a := (classicalRestrictionLinearEquiv b).symm u
  have he := classicalIntervalExtension_energy b (classicalIntervalRestriction a.val)
    (classicalIntervalRestriction_mem b a.val a.property)
  rw [classicalIntervalExtension_classicalIntervalRestriction b a.val a.property] at he
  change ‖sobolevEnergyEmbedding a.val.1‖ = Real.sqrt (classicalIntervalEnergy
    (classicalIntervalRestriction a.val))
  rw [norm_sobolevEnergyEmbedding, he]

/-- Every original classical input receives precisely its physical component-sum Sobolev norm. -/
@[simp] theorem norm_classicalDomainOfFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) :
    ‖classicalDomainOfFunction b f hf‖ = classicalIntervalNorm f := by
  rw [norm_classicalDomainRepresentative]
  apply congrArg Real.sqrt
  apply classicalIntervalEnergy_congr
  intro x hx
  exact classicalDomainRepresentative_apply b (classicalDomainOfFunction b f hf) ⟨x, hx⟩

/-- The Fourier extension is contractive from the physical interval norm. -/
theorem norm_classicalExtensionLinearEquiv_le (b : BoundaryCondition)
    (u : ClassicalIntervalDomain b) : ‖(classicalRestrictionLinearEquiv b).symm u‖ ≤ ‖u‖ := by
  rw [norm_classicalDomainRepresentative]
  exact (classicalIntervalRestriction_norm_bounds b _
    ((classicalRestrictionLinearEquiv b).symm u).property).1

/-- Physical restriction is bounded from the maximum weighted pair norm. -/
theorem norm_classicalRestrictionLinearEquiv_le (b : BoundaryCondition)
    (a : ↥(domain (p := 2) b)) :
    ‖classicalRestrictionLinearEquiv b a‖ ≤ Real.sqrt 2 * Real.pi * ‖a‖ := by
  rw [norm_classicalDomainRepresentative]
  change classicalIntervalNorm (classicalIntervalRestriction
    ((classicalRestrictionLinearEquiv b).symm (classicalRestrictionLinearEquiv b a)).val) ≤ _
  rw [LinearEquiv.symm_apply_apply]
  exact (classicalIntervalRestriction_norm_bounds b a.val a.property).2

/-- Lemma 4.2: the original classical domain and its weighted boundary domain are isomorphic. -/
def classicalIntervalEquiv (b : BoundaryCondition) :
    ClassicalIntervalDomain b ≃L[ℂ] ↥(domain (p := 2) b) :=
  (classicalRestrictionLinearEquiv b).symm.toContinuousLinearEquivOfBounds 1
    (Real.sqrt 2 * Real.pi)
    (fun u => by simpa only [one_mul] using norm_classicalExtensionLinearEquiv_le b u)
    (norm_classicalRestrictionLinearEquiv_le b)

/-- The continuous equivalence extends original functions using their actual Fourier integrals. -/
@[simp] theorem classicalIntervalEquiv_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalIntervalDomain b f) :
    classicalIntervalEquiv b (classicalDomainOfFunction b f hf) =
      ⟨classicalIntervalExtension b f hf, classicalIntervalExtension_mem b f hf⟩ :=
  classicalRestrictionLinearEquiv_symm_ofFunction b f hf

/-- The inverse continuous equivalence is physical restriction at every closed-interval point. -/
@[simp] theorem classicalIntervalEquiv_symm_apply (b : BoundaryCondition)
    (a : ↥(domain (p := 2) b)) (x : Icc (0 : ℝ) 1) :
    ((classicalIntervalEquiv b).symm a).val x = classicalIntervalRestriction a.val x.val := rfl

/-- Extension has operator norm at most one in the exact physical norm. -/
theorem norm_classicalIntervalEquiv_le (b : BoundaryCondition) :
    ‖(classicalIntervalEquiv b).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  change ‖(classicalRestrictionLinearEquiv b).symm u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using norm_classicalExtensionLinearEquiv_le b u

/-- The inverse operator norm retains the explicit physical normalization constant. -/
theorem norm_classicalIntervalEquiv_symm_le (b : BoundaryCondition) :
    ‖(classicalIntervalEquiv b).symm.toContinuousLinearMap‖ ≤ Real.sqrt 2 * Real.pi := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_classicalRestrictionLinearEquiv_le b

/-- Completeness follows through the bounded extension/restriction equivalence. -/
instance (b : BoundaryCondition) : CompleteSpace (ClassicalIntervalDomain b) := by
  let e : ClassicalIntervalDomain b ≃ᵤ ↥(domain (p := 2) b) :=
    { toEquiv := (classicalIntervalEquiv b).toEquiv
      uniformContinuous_toFun := (classicalIntervalEquiv b).toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun := (classicalIntervalEquiv b).symm.toContinuousLinearMap.uniformContinuous }
  exact e.completeSpace_iff.mpr inferInstance

end NLS.ZakharovShabat.BoundaryCondition
