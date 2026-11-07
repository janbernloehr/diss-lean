import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Tactic.FieldSimp

/-! # Restriction of a full-dual isomorphism to a closed hyperplane

A nonzero scalar trace of the full inverse applied to the trace functional
is the exact Schur condition. A bounded extension of hyperplane functionals
then gives an explicit two-sided inverse, retaining the full continuous dual.
-/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Full-dual restriction to the exact trace kernel. -/
def hyperplaneDualRestriction (tau : V →L[𝕜] 𝕜) :
    (V →L[𝕜] 𝕜) →L[𝕜] (tau.ker →L[𝕜] 𝕜) where
  toFun F := F.comp tau.ker.subtypeL
  map_add' F G := by ext x; rfl
  map_smul' c F := by ext x; rfl
  cont := (continuous_id : Continuous (fun F : V →L[𝕜] 𝕜 => F)).clm_comp_const tau.ker.subtypeL

/-- The full bounded form restricted to vectors and tests in the hyperplane. -/
def hyperplaneDualOperator (B : V ≃L[𝕜] (V →L[𝕜] 𝕜)) (tau : V →L[𝕜] 𝕜) :
    tau.ker →L[𝕜] (tau.ker →L[𝕜] 𝕜) :=
  (hyperplaneDualRestriction tau).comp (B.toContinuousLinearMap.comp tau.ker.subtypeL)

/-- A functional vanishing on a trace kernel is exactly a scalar trace functional. -/
theorem fullDual_eq_smul_of_ker_vanishes (tau F : V →L[𝕜] 𝕜) (e : V) (he : tau e = 1)
    (hF : ∀ x : tau.ker, F x.val = 0) : F = F e • tau := by
  apply ContinuousLinearMap.ext
  intro x
  have hx : x-tau x • e ∈ tau.ker := by
    change tau (x-tau x • e) = 0
    rw [map_sub, map_smul, he, smul_eq_mul, mul_one, sub_self]
  have h := hF ⟨x-tau x • e,hx⟩
  change F (x-tau x • e) = 0 at h
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h
  change F x = F e*tau x
  exact h.trans (mul_comm _ _)

/-- The exact scalar Schur condition ensures injectivity of the whole restricted form. -/
theorem hyperplaneDualOperator_injective (B : V ≃L[𝕜] (V →L[𝕜] 𝕜)) (tau : V →L[𝕜] 𝕜)
    (ht : tau (B.symm tau) ≠ 0) : Function.Injective (hyperplaneDualOperator B tau) := by
  have hzero (f : tau.ker) (hf : hyperplaneDualOperator B tau f = 0) : f = 0 := by
    let g := B.symm tau
    let e := (tau g)⁻¹ • g
    have he : tau e = 1 := by
      change tau ((tau g)⁻¹ • g) = 1
      rw [map_smul, smul_eq_mul, inv_mul_cancel₀ ht]
    have hF : B f.val = B f.val e • tau := by
      apply fullDual_eq_smul_of_ker_vanishes tau (B f.val) e he
      intro x
      exact congrArg (fun F : tau.ker →L[𝕜] 𝕜 => F x) hf
    have hrep : f.val = B f.val e • g := by
      have h := congrArg B.symm hF
      simpa only [ContinuousLinearEquiv.symm_apply_apply, map_smul] using h
    have hc : B f.val e = 0 := by
      have h := congrArg tau hrep
      rw [show tau f.val = 0 from f.property, map_smul, smul_eq_mul] at h
      exact (mul_eq_zero.mp h.symm).resolve_right ht
    apply Subtype.ext
    change f.val = 0
    rw [hrep, hc, zero_smul]
  intro f g h
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, h, sub_self]

/-- The inverse solution before restriction, with its exact rank-one trace correction. -/
def hyperplaneDualInverseLift (B : V ≃L[𝕜] (V →L[𝕜] 𝕜)) (tau : V →L[𝕜] 𝕜)
    (E : (tau.ker →L[𝕜] 𝕜) →L[𝕜] (V →L[𝕜] 𝕜)) : (tau.ker →L[𝕜] 𝕜) →L[𝕜] V :=
  let S := B.symm.toContinuousLinearMap.comp E
  S-(tau (B.symm tau))⁻¹ • ((tau.comp S).smulRight (B.symm tau))

theorem hyperplaneDualInverseLift_trace
    (B : V ≃L[𝕜] (V →L[𝕜] 𝕜)) (tau : V →L[𝕜] 𝕜)
    (E : (tau.ker →L[𝕜] 𝕜) →L[𝕜] (V →L[𝕜] 𝕜))
    (ht : tau (B.symm tau) ≠ 0) (F : tau.ker →L[𝕜] 𝕜) :
    tau (hyperplaneDualInverseLift B tau E F) = 0 := by
  change tau (B.symm (E F)-(tau (B.symm tau))⁻¹ •
    (tau (B.symm (E F)) • B.symm tau)) = 0
  rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  field_simp
  simp only [sub_self, mul_zero]

/-- The correction is a bounded map into the actual trace kernel. -/
def hyperplaneDualInverse (B : V ≃L[𝕜] (V →L[𝕜] 𝕜)) (tau : V →L[𝕜] 𝕜)
    (E : (tau.ker →L[𝕜] 𝕜) →L[𝕜] (V →L[𝕜] 𝕜))
    (ht : tau (B.symm tau) ≠ 0) : (tau.ker →L[𝕜] 𝕜) →L[𝕜] tau.ker :=
  (hyperplaneDualInverseLift B tau E).codRestrict tau.ker
    (fun F => hyperplaneDualInverseLift_trace B tau E ht F)

/-- Every full hyperplane-dual input is solved, without narrowing its test class. -/
theorem hyperplaneDualInverse_right
    (B : V ≃L[𝕜] (V →L[𝕜] 𝕜)) (tau : V →L[𝕜] 𝕜)
    (E : (tau.ker →L[𝕜] 𝕜) →L[𝕜] (V →L[𝕜] 𝕜))
    (ht : tau (B.symm tau) ≠ 0)
    (hE : ∀ (F : tau.ker →L[𝕜] 𝕜) (x : tau.ker), E F x.val = F x)
    (F : tau.ker →L[𝕜] 𝕜) :
    hyperplaneDualOperator B tau (hyperplaneDualInverse B tau E ht F) = F := by
  apply ContinuousLinearMap.ext
  intro x
  change B (B.symm (E F)-(tau (B.symm tau))⁻¹ •
    (tau (B.symm (E F)) • B.symm tau)) x.val = F x
  rw [map_sub, map_smul, map_smul, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  change E F x.val-(tau (B.symm tau))⁻¹*(tau (B.symm (E F))*tau x.val) = F x
  rw [show tau x.val = 0 from x.property, mul_zero, mul_zero, sub_zero]
  exact hE F x

/-- The scalar Schur condition and a bounded full-dual extension give an actual
Banach-space isomorphism of the hyperplane with its ENTIRE continuous dual. -/
def hyperplaneDualIsomorphism
    (B : V ≃L[𝕜] (V →L[𝕜] 𝕜)) (tau : V →L[𝕜] 𝕜)
    (E : (tau.ker →L[𝕜] 𝕜) →L[𝕜] (V →L[𝕜] 𝕜))
    (ht : tau (B.symm tau) ≠ 0)
    (hE : ∀ (F : tau.ker →L[𝕜] 𝕜) (x : tau.ker), E F x.val = F x) :
    tau.ker ≃L[𝕜] (tau.ker →L[𝕜] 𝕜) where
  toLinearEquiv :=
    { toLinearMap := (hyperplaneDualOperator B tau).toLinearMap
      invFun := hyperplaneDualInverse B tau E ht
      left_inv f := hyperplaneDualOperator_injective B tau ht
        (hyperplaneDualInverse_right B tau E ht hE (hyperplaneDualOperator B tau f))
      right_inv := hyperplaneDualInverse_right B tau E ht hE }
  continuous_toFun := (hyperplaneDualOperator B tau).continuous
  continuous_invFun := (hyperplaneDualInverse B tau E ht).continuous

end NLS.FunctionalAnalysis
