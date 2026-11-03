import NLS.Fourier.UnitIntervalDirichletModes
import NLS.KdV.UnitHillFreeGreen
import NLS.KdV.SingularDirichletPencil
import NLS.FunctionalAnalysis.HyperplaneDualIsomorphism
import NLS.Fourier.PeriodicSingularMultiplicationFamily

/-! # The actual massive free Dirichlet isomorphism

The inverse acts on the FULL continuous zero-trace H1 dual, using a verified
rank-one endpoint correction. Its forward map is exactly the native positive
free Laplacian plus domain inclusion, with all original normalizations retained.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.FunctionalAnalysis
open NLS.ZakharovShabat

/-- Every native full-dual datum has an explicit bounded extension to unit-period H1. -/
def unitDirichletFullDualExtension : UnitDirichletHminus →L[ℂ] (ScalarDomain 2 →L[ℂ] ℂ) where
  toFun F := F.comp unitDirichletProjection
  map_add' F G := by ext x; rfl
  map_smul' c F := by ext x; rfl
  cont := (continuous_id : Continuous (fun F : UnitDirichletHminus => F)).clm_comp_const
    unitDirichletProjection

theorem unitDirichletFullDualExtension_apply (F : UnitDirichletHminus) (f : UnitDirichletH1) :
    unitDirichletFullDualExtension F f.val = F f := by
  change F (unitDirichletProjection f.val) = F f
  rw [unitDirichletProjection_subtype]

/-- The free endpoint Schur correction gives an actual isomorphism onto the full native base. -/
def singularDirichletFreeIsomorphism : UnitDirichletH1 ≃L[ℂ] UnitDirichletHminus :=
  hyperplaneDualIsomorphism unitHillFreeDualIsomorphism unitDirichletTrace
    unitDirichletFullDualExtension unitDirichletTrace_unitHillFreeGreen_ne_zero
      unitDirichletFullDualExtension_apply

/-- The original singular Hill expression at zero potential is exactly its physical Laplacian. -/
theorem singularHillOperator_zero :
    singularHillOperator (0 : FourierLebesgueSpace (2:ℝ) (-1) 2) = singularHillLaplacian := by
  have hzero : hminusOneMultiplication (0 : FourierLebesgueSpace (2:ℝ) (-1) 2) = 0 :=
    (hminusOneMultiplicationFamily (L := 2)).map_zero
  change singularHillLaplacian+hminusOneMultiplication (0 : FourierLebesgueSpace (2:ℝ) (-1) 2) = _
  rw [hzero, add_zero]

/-- The full unit-period free form is the unchanged native free residual before trace restriction. -/
theorem unitHillFreeDualIsomorphism_eq_DirichletResidual (f : UnitDirichletH1) :
    unitHillFreeDualIsomorphism f.val = singularDirichletResidual 0 (-1) f := by
  have hv : singularHillOperator (0 : FourierLebesgueSpace (2:ℝ) (-1) 2)
      (unitDirichletOriginalH1 f)-(-1:ℂ) • singularHillDomainInclusion (unitDirichletOriginalH1 f) =
        singularHillFreeShift (unitDirichletOriginalH1 f) := by
    rw [singularHillOperator_zero, neg_one_smul, sub_neg_eq_add]
    rfl
  apply scalarMode_dual_ext
  intro n
  rw [unitHillFreeDualIsomorphism_mode, singularDirichletResidual_mode, hv,
    show 2*n = -(2*(-n)) by ring, singularHillFreeShift_coefficient,
    unitDirichletOriginalH1_coefficient, Coeff.periodDouble_even, scalarInclusion_apply]

/-- The isomorphism is the EXACT native massive free Dirichlet operator. -/
theorem singularDirichletFreeIsomorphism_apply (f : UnitDirichletH1) :
    singularDirichletFreeIsomorphism f =
      singularDirichletOperator 0 f+singularDirichletDomainInclusion f := by
  change unitDirichletDualRestriction (unitHillFreeDualIsomorphism f.val) = _
  rw [unitHillFreeDualIsomorphism_eq_DirichletResidual, singularDirichletResidual_restriction]
  module

/-- Every original H1 vector is recovered by the actual native free inverse. -/
theorem singularDirichletFreeIsomorphism_symm_left (f : UnitDirichletH1) :
    singularDirichletFreeIsomorphism.symm
      (singularDirichletOperator 0 f+singularDirichletDomainInclusion f) = f := by
  rw [← singularDirichletFreeIsomorphism_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- Every full native H-minus-one datum is solved by the actual free Dirichlet operator. -/
theorem singularDirichletFreeIsomorphism_symm_right (F : UnitDirichletHminus) :
    singularDirichletOperator 0 (singularDirichletFreeIsomorphism.symm F)+
      singularDirichletDomainInclusion (singularDirichletFreeIsomorphism.symm F) = F := by
  rw [← singularDirichletFreeIsomorphism_apply, ContinuousLinearEquiv.apply_symm_apply]

end NLS.KdV
