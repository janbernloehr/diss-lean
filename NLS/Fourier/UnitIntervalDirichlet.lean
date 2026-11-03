import NLS.Fourier.PeriodOneSobolev
import NLS.Fourier.PeriodicSobolevDuality
import NLS.ZakharovShabat.ClassicalNLSSobolevEnergy

/-! # Zero-trace unit-interval Sobolev data

Unit-period H1 coefficients give continuous, absolutely continuous interval
representatives with square-integrable derivative. The kernel of evaluation
at zero has zero trace at both endpoints. Its full continuous dual is the
Dirichlet H-minus-one base, rather than an L2 base. Restricting a functional
to this kernel kills exactly the multiples of endpoint evaluation.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.Fourier
open ZakharovShabat PeriodicFourierLebesgue SmoothPeriodicTest

/-- Endpoint evaluation in the unit-period H1 norm. -/
def unitDirichletTrace : ScalarDomain 2 →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ (0 : AddCircle (2 : ℝ))).comp periodOneSobolevSynthesis

@[simp] theorem unitDirichletTrace_apply (f : ScalarDomain 2) :
    unitDirichletTrace f = periodOneSobolevSynthesis f (0 : AddCircle (2 : ℝ)) := rfl

@[simp] theorem unitDirichletTrace_scalarMode (n : ℤ) (c : ℂ) :
    unitDirichletTrace (scalarMode n c) = c := by
  change periodOneSobolevSynthesis (scalarMode n c) ((0 : ℝ) : AddCircle (2 : ℝ)) = c
  simp only [periodOneSobolevSynthesis_scalarMode, wave_at_zero, mul_one]

/-- Zero trace at both endpoints, encoded in unit-period coefficients. -/
def unitDirichletSubspace : Submodule ℂ (ScalarDomain 2) := unitDirichletTrace.ker

abbrev UnitDirichletH1 := ↥unitDirichletSubspace
abbrev UnitDirichletHminus := UnitDirichletH1 →L[ℂ] ℂ

theorem isClosed_unitDirichletSubspace : IsClosed (unitDirichletSubspace : Set (ScalarDomain 2)) :=
  unitDirichletTrace.isClosed_ker

instance : CompleteSpace UnitDirichletH1 := isClosed_unitDirichletSubspace.completeSpace_coe

/-- The representative on the real line is used only through its interval values. -/
def unitDirichletRepresentative (f : UnitDirichletH1) (x : ℝ) : ℂ :=
  periodOneSobolevSynthesis f.val (x : AddCircle (2 : ℝ))

@[simp] theorem unitDirichletRepresentative_zero (f : UnitDirichletH1) :
    unitDirichletRepresentative f 0 = 0 := f.property

@[simp] theorem unitDirichletRepresentative_one (f : UnitDirichletH1) :
    unitDirichletRepresentative f 1 = 0 := by
  have h := periodOneSobolevSynthesis_periodic f.val 0
  change unitDirichletRepresentative f (0+1) = unitDirichletRepresentative f 0 at h
  simpa only [zero_add, unitDirichletRepresentative_zero] using h

theorem absolutelyContinuous_unitDirichletRepresentative (f : UnitDirichletH1) :
    AbsolutelyContinuousOnInterval (unitDirichletRepresentative f) 0 1 :=
  absolutelyContinuous_periodOneSobolevSynthesis f.val

theorem memLp_deriv_unitDirichletRepresentative (f : UnitDirichletH1) :
    MemLp (deriv (unitDirichletRepresentative f)) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_deriv_periodOneSobolevSynthesis f.val

/-- Physical conjugation preserves both Dirichlet endpoint conditions. -/
def unitDirichletConjugate (f : UnitDirichletH1) : UnitDirichletH1 :=
  ⟨sobolevConjugateCLM f.val, by
    change periodOneSobolevSynthesis (sobolevConjugateCLM f.val)
      ((0 : ℝ) : AddCircle (2 : ℝ)) = 0
    rw [periodOneSobolevSynthesis_conjugate]
    change star (unitDirichletRepresentative f 0) = 0
    rw [unitDirichletRepresentative_zero, star_zero]⟩

@[simp] theorem unitDirichletConjugate_coefficient (f : UnitDirichletH1) (n : ℤ) :
    (unitDirichletConjugate f).val.val n = star (f.val.val (-n)) :=
  sobolevConjugateCLM_apply f.val n

/-- Full bounded restriction to the Dirichlet domain. -/
def unitDirichletDualRestriction :
    (ScalarDomain 2 →L[ℂ] ℂ) →L[ℂ] UnitDirichletHminus where
  toFun F := F.comp unitDirichletSubspace.subtypeL
  map_add' F G := by ext f; rfl
  map_smul' c F := by ext f; rfl
  cont := (continuous_id : Continuous (fun F : ScalarDomain 2 →L[ℂ] ℂ => F)).clm_comp_const
    unitDirichletSubspace.subtypeL

@[simp] theorem unitDirichletDualRestriction_apply
    (F : ScalarDomain 2 →L[ℂ] ℂ) (f : UnitDirichletH1) :
    unitDirichletDualRestriction F f = F f.val := rfl

/-- Removing the endpoint value is a bounded projection onto the zero-trace domain. -/
def unitDirichletProjection : ScalarDomain 2 →L[ℂ] UnitDirichletH1 :=
by
  let P : ScalarDomain 2 →L[ℂ] ScalarDomain 2 :=
    ContinuousLinearMap.id ℂ (ScalarDomain 2) -
      unitDirichletTrace.smulRight (scalarMode 0 1)
  have hP (f : ScalarDomain 2) : unitDirichletTrace (P f) = 0 := by
    simp only [P, _root_.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, map_sub, map_smul,
      unitDirichletTrace_scalarMode, smul_eq_mul, mul_one, sub_self]
  exact P.codRestrict unitDirichletSubspace (fun f => hP f)

@[simp] theorem unitDirichletProjection_val (f : ScalarDomain 2) :
    (unitDirichletProjection f).val = f-unitDirichletTrace f • scalarMode 0 1 := rfl

@[simp] theorem unitDirichletProjection_subtype (f : UnitDirichletH1) :
    unitDirichletProjection f.val = f := by
  apply Subtype.ext
  change f.val-unitDirichletTrace f.val • scalarMode 0 1 = f.val
  rw [show unitDirichletTrace f.val = 0 from f.property, zero_smul, sub_zero]

/-- Every continuous Dirichlet functional extends to the full unit-period H1 space. -/
theorem unitDirichletDualRestriction_surjective :
    Function.Surjective unitDirichletDualRestriction := by
  intro F
  refine ⟨F.comp unitDirichletProjection, ?_⟩
  ext f
  change F (unitDirichletProjection f.val) = F f
  rw [unitDirichletProjection_subtype]

/-- The boundary defect is exactly one endpoint functional; it cannot be
silently set to zero when recovering a quasi-derivative from a weak equation. -/
theorem unitDirichletDualRestriction_eq_zero_iff (F : ScalarDomain 2 →L[ℂ] ℂ) :
    unitDirichletDualRestriction F = 0 ↔
      F = F (scalarMode 0 1) • unitDirichletTrace := by
  constructor
  · intro h
    ext f
    have hg := congrArg (fun G : UnitDirichletHminus => G (unitDirichletProjection f)) h
    change F (f-unitDirichletTrace f • scalarMode 0 1) = 0 at hg
    simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hg
    change F f = F (scalarMode 0 1) * unitDirichletTrace f
    exact hg.trans (mul_comm _ _)
  · intro h
    ext f
    change F f.val = 0
    rw [h]
    change F (scalarMode 0 1) * unitDirichletTrace f.val = 0
    rw [show unitDirichletTrace f.val = 0 from f.property, mul_zero]

/-- Unit-period H1 in the unchanged original period-two distribution space. -/
def unitSobolevOriginalH1 : ScalarDomain 2 →L[ℂ] FourierLebesgueSpace (2 : ℝ) 1 2 :=
  (sobolevCoefficients 1 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    Coeff.periodDoubleSobolevCLM

@[simp] theorem unitSobolevOriginalH1_coefficient (f : ScalarDomain 2) (n : ℤ) :
    (unitSobolevOriginalH1 f).val (mode (-n)) = Coeff.periodDouble (scalarInclusion f) n := by
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm _)).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The same unit-interval function in the unchanged period-two original H1 space. -/
def unitDirichletOriginalH1 : UnitDirichletH1 →L[ℂ] FourierLebesgueSpace (2 : ℝ) 1 2 :=
  unitSobolevOriginalH1.comp unitDirichletSubspace.subtypeL

@[simp] theorem unitDirichletOriginalH1_coefficient (f : UnitDirichletH1) (n : ℤ) :
    (unitDirichletOriginalH1 f).val (mode (-n)) = Coeff.periodDouble (scalarInclusion f.val) n := by
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm _)).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem unitDirichletOriginalH1_injective : Function.Injective unitDirichletOriginalH1 := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  funext n
  have hn := congrArg (fun v : FourierLebesgueSpace (2 : ℝ) 1 2 => v.val (mode (-(2*n)))) h
  simpa only [unitDirichletOriginalH1_coefficient, Coeff.periodDouble_even,
    scalarInclusion_apply] using hn

end NLS.Fourier
