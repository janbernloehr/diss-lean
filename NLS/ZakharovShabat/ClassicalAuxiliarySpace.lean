import NLS.ZakharovShabat.ClassicalAuxiliaryExtension
import NLS.ZakharovShabat.ClassicalIntervalIsomorphism

/-!
# The original normed auxiliary interval domains

Elements are actual functions on the closed interval, characterized by the
original auxiliary H¹ endpoint conditions. The norm is exactly the physical
component-sum H¹ norm. Phase rotation is an isometry from the ordinary domain,
and actual Fourier extension is a continuous linear equivalence onto the
auxiliary weighted domain, with the same explicit bounds.
-/

noncomputable section
open Set NLS.Fourier
namespace NLS.ZakharovShabat

/-- Pointwise phase rotation on functions on the original closed interval. -/
def intervalFunctionPhase : (Icc (0 : ℝ) 1 → ℂ × ℂ) ≃ₗ[ℂ] (Icc (0 : ℝ) 1 → ℂ × ℂ) where
  toFun f x := auxiliaryPhase ℂ (f x)
  invFun f x := (auxiliaryPhase ℂ).symm (f x)
  left_inv f := funext fun x => (auxiliaryPhase ℂ).symm_apply_apply (f x)
  right_inv f := funext fun x => (auxiliaryPhase ℂ).apply_symm_apply (f x)
  map_add' f g := funext fun x => map_add (auxiliaryPhase ℂ) (f x) (g x)
  map_smul' c f := funext fun x => map_smul (auxiliaryPhase ℂ) c (f x)

namespace BoundaryCondition

/-- The original auxiliary interval functions, with pointwise linear operations. -/
def classicalAuxiliarySubmodule (b : BoundaryCondition) : Submodule ℂ (Icc (0 : ℝ) 1 → ℂ × ℂ) :=
  (classicalIntervalSubmodule b).map intervalFunctionPhase.toLinearMap

theorem mem_classicalAuxiliarySubmodule_iff (b : BoundaryCondition) (u : Icc (0 : ℝ) 1 → ℂ × ℂ) :
    u ∈ classicalAuxiliarySubmodule b ↔ ∃ f : ℝ → ℂ × ℂ,
      HasClassicalAuxiliaryDomain b f ∧ ∀ x : Icc (0 : ℝ) 1, u x = f x.val := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨f, hf, he⟩ := (mem_classicalIntervalSubmodule_iff b v).mp hv
    refine ⟨physicalAuxiliaryPhase f, (hasClassicalAuxiliaryDomain_phase_iff b f).mpr hf, ?_⟩
    intro x
    exact congrArg (auxiliaryPhase ℂ) (he x)
  · rintro ⟨f, hf, he⟩
    refine ⟨fun x => physicalAuxiliaryPhase.symm f x.val, ?_, ?_⟩
    · exact (mem_classicalIntervalSubmodule_iff b _).mpr
        ⟨physicalAuxiliaryPhase.symm f, (hasClassicalAuxiliaryDomain_iff b f).mp hf, fun _ => rfl⟩
    · funext x
      exact ((auxiliaryPhase ℂ).apply_symm_apply (f x.val)).trans (he x).symm

/-- Actual auxiliary endpoint-domain functions on `[0,1]`. -/
def ClassicalAuxiliaryDomain (b : BoundaryCondition) := ↥(classicalAuxiliarySubmodule b)

instance (b : BoundaryCondition) : AddCommGroup (ClassicalAuxiliaryDomain b) :=
  inferInstanceAs (AddCommGroup ↥(classicalAuxiliarySubmodule b))
instance (b : BoundaryCondition) : Module ℂ (ClassicalAuxiliaryDomain b) :=
  inferInstanceAs (Module ℂ ↥(classicalAuxiliarySubmodule b))

/-- Algebraic phase rotation between the two original endpoint domains. -/
def classicalAuxiliaryDomainLinearEquiv (b : BoundaryCondition) :
    ClassicalIntervalDomain b ≃ₗ[ℂ] ClassicalAuxiliaryDomain b :=
  intervalFunctionPhase.submoduleMap (classicalIntervalSubmodule b)

instance (b : BoundaryCondition) : NormedAddCommGroup (ClassicalAuxiliaryDomain b) :=
  NormedAddCommGroup.induced _ _ (classicalAuxiliaryDomainLinearEquiv b).symm.toLinearMap
    (classicalAuxiliaryDomainLinearEquiv b).symm.injective
instance (b : BoundaryCondition) : NormedSpace ℂ (ClassicalAuxiliaryDomain b) :=
  NormedSpace.induced ℂ _ _ (classicalAuxiliaryDomainLinearEquiv b).symm.toLinearMap

/-- The physical phase rotation is isometric in the original Sobolev norm. -/
def classicalAuxiliaryDomainPhase (b : BoundaryCondition) :
    ClassicalIntervalDomain b ≃ₗᵢ[ℂ] ClassicalAuxiliaryDomain b :=
  { classicalAuxiliaryDomainLinearEquiv b with
    norm_map' f := by
      change ‖(classicalAuxiliaryDomainLinearEquiv b).symm (classicalAuxiliaryDomainLinearEquiv b f)‖ = ‖f‖
      rw [LinearEquiv.symm_apply_apply] }

/-- Passing from an original auxiliary function to its actual closed-interval values. -/
def classicalAuxiliaryDomainOfFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) : ClassicalAuxiliaryDomain b :=
  ⟨fun x => f x.val, (mem_classicalAuxiliarySubmodule_iff b _).mpr ⟨f, hf, fun _ => rfl⟩⟩

/-- The canonical representative is the phase of the ordinary canonical representative. -/
def classicalAuxiliaryDomainRepresentative (b : BoundaryCondition) (u : ClassicalAuxiliaryDomain b) : ℝ → ℂ × ℂ :=
  physicalAuxiliaryPhase (classicalDomainRepresentative b ((classicalAuxiliaryDomainPhase b).symm u))

theorem classicalAuxiliaryDomainRepresentative_mem (b : BoundaryCondition) (u : ClassicalAuxiliaryDomain b) :
    HasClassicalAuxiliaryDomain b (classicalAuxiliaryDomainRepresentative b u) :=
  (hasClassicalAuxiliaryDomain_phase_iff b _).mpr (classicalDomainRepresentative_mem b _)

theorem classicalAuxiliaryDomainRepresentative_apply (b : BoundaryCondition) (u : ClassicalAuxiliaryDomain b)
    (x : Icc (0 : ℝ) 1) : classicalAuxiliaryDomainRepresentative b u x.val = u.val x := by
  change auxiliaryPhase ℂ (classicalDomainRepresentative b ((classicalAuxiliaryDomainPhase b).symm u) x.val) = _
  rw [classicalDomainRepresentative_apply]
  exact (auxiliaryPhase ℂ).apply_symm_apply (u.val x)

/-- Phase multiplication preserves both the value and derivative contributions to the physical norm. -/
theorem classicalIntervalNorm_physicalAuxiliaryPhase (f : ℝ → ℂ × ℂ) :
    classicalIntervalNorm (physicalAuxiliaryPhase f) = classicalIntervalNorm f := by
  simp only [classicalIntervalNorm, classicalIntervalEnergy, physicalAuxiliaryPhase_apply,
    intervalH1Energy, deriv_const_mul_field', norm_mul, Complex.norm_I, one_mul]

/-- The induced auxiliary norm equals the actual component-sum physical H¹ norm. -/
theorem norm_classicalAuxiliaryDomainRepresentative (b : BoundaryCondition) (u : ClassicalAuxiliaryDomain b) :
    ‖u‖ = classicalIntervalNorm (classicalAuxiliaryDomainRepresentative b u) := by
  rw [classicalAuxiliaryDomainRepresentative, classicalIntervalNorm_physicalAuxiliaryPhase]
  exact norm_classicalDomainRepresentative b ((classicalAuxiliaryDomainPhase b).symm u)

@[simp] theorem norm_classicalAuxiliaryDomainOfFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) :
    ‖classicalAuxiliaryDomainOfFunction b f hf‖ = classicalIntervalNorm f := by
  rw [norm_classicalAuxiliaryDomainRepresentative]
  apply congrArg Real.sqrt
  apply classicalIntervalEnergy_congr
  intro x hx
  exact classicalAuxiliaryDomainRepresentative_apply b (classicalAuxiliaryDomainOfFunction b f hf) ⟨x, hx⟩

/-- The actual auxiliary Sobolev extension and physical restriction are continuous linear inverses. -/
def classicalAuxiliaryIntervalEquiv (b : BoundaryCondition) :
    ClassicalAuxiliaryDomain b ≃L[ℂ] auxiliaryDomain (p := 2) b :=
  ((classicalAuxiliaryDomainPhase b).symm.toContinuousLinearEquiv.trans (classicalIntervalEquiv b)).trans
    (auxiliaryDomainEquiv b).toContinuousLinearEquiv

@[simp] theorem classicalAuxiliaryDomainPhase_symm_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) :
    (classicalAuxiliaryDomainPhase b).symm (classicalAuxiliaryDomainOfFunction b f hf) =
      classicalDomainOfFunction b (physicalAuxiliaryPhase.symm f) ((hasClassicalAuxiliaryDomain_iff b f).mp hf) := rfl

/-- The forward equivalence is the previously constructed actual Fourier extension. -/
@[simp] theorem classicalAuxiliaryIntervalEquiv_ofFunction (b : BoundaryCondition) (f : ℝ → ℂ × ℂ)
    (hf : HasClassicalAuxiliaryDomain b f) :
    classicalAuxiliaryIntervalEquiv b (classicalAuxiliaryDomainOfFunction b f hf) =
      ⟨classicalAuxiliaryExtension b f hf, classicalAuxiliaryExtension_mem b f hf⟩ := by
  change auxiliaryDomainEquiv b (classicalIntervalEquiv b
    ((classicalAuxiliaryDomainPhase b).symm (classicalAuxiliaryDomainOfFunction b f hf))) = _
  rw [classicalAuxiliaryDomainPhase_symm_ofFunction, classicalIntervalEquiv_ofFunction]
  rfl

/-- The inverse continuous equivalence is actual physical restriction at every original point. -/
@[simp] theorem classicalAuxiliaryIntervalEquiv_symm_apply (b : BoundaryCondition)
    (a : auxiliaryDomain (p := 2) b) (x : Icc (0 : ℝ) 1) :
    ((classicalAuxiliaryIntervalEquiv b).symm a).val x = classicalIntervalRestriction a.val x.val := by
  change physicalAuxiliaryPhase (classicalIntervalRestriction ((auxiliaryPhase (ScalarDomain 2)).symm a.val)) x.val = _
  rw [← classicalIntervalRestriction_auxiliaryPhase, LinearIsometryEquiv.apply_symm_apply]

/-- Extension retains the explicit operator-norm bound in the physical H¹ norm. -/
theorem norm_classicalAuxiliaryIntervalEquiv_le (b : BoundaryCondition) :
    ‖(classicalAuxiliaryIntervalEquiv b).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  change ‖auxiliaryDomainEquiv b (classicalIntervalEquiv b ((classicalAuxiliaryDomainPhase b).symm u))‖ ≤ _
  rw [(auxiliaryDomainEquiv b).norm_map]
  simpa only [ContinuousLinearEquiv.coe_coe, (classicalAuxiliaryDomainPhase b).symm.norm_map, one_mul] using
    (classicalIntervalEquiv b).toContinuousLinearMap.le_of_opNorm_le (norm_classicalIntervalEquiv_le b)
      ((classicalAuxiliaryDomainPhase b).symm u)

/-- Restriction has the same explicit inverse bound as the ordinary physical domain. -/
theorem norm_classicalAuxiliaryIntervalEquiv_symm_le (b : BoundaryCondition) :
    ‖(classicalAuxiliaryIntervalEquiv b).symm.toContinuousLinearMap‖ ≤ Real.sqrt 2 * Real.pi := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  change ‖classicalAuxiliaryDomainPhase b ((classicalIntervalEquiv b).symm ((auxiliaryDomainEquiv b).symm a))‖ ≤ _
  rw [(classicalAuxiliaryDomainPhase b).norm_map]
  simpa only [ContinuousLinearEquiv.coe_coe, (auxiliaryDomainEquiv b).symm.norm_map] using
    (classicalIntervalEquiv b).symm.toContinuousLinearMap.le_of_opNorm_le (norm_classicalIntervalEquiv_symm_le b)
      ((auxiliaryDomainEquiv b).symm a)

instance (b : BoundaryCondition) : CompleteSpace (ClassicalAuxiliaryDomain b) := by
  let e : ClassicalAuxiliaryDomain b ≃ᵤ ClassicalIntervalDomain b :=
    { toEquiv := (classicalAuxiliaryDomainPhase b).symm.toEquiv
      uniformContinuous_toFun := (classicalAuxiliaryDomainPhase b).symm.isometry.uniformContinuous
      uniformContinuous_invFun := (classicalAuxiliaryDomainPhase b).isometry.uniformContinuous }
  exact e.completeSpace_iff.mpr inferInstance

end BoundaryCondition
end NLS.ZakharovShabat
